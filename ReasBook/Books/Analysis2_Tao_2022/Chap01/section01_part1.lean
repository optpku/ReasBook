/-
Authors: Zichen Wang, Wanli Ma, Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap01
section Section01

/-- Theorem 1.1: summing `(-a i) * b i` gives the negative of the sum of `a i * b i`. -/
lemma sum_neg_mul_eq_neg_sum_mul (n : ℕ) (a b : Fin n → ℝ) :
    Finset.univ.sum (fun i : Fin n => (-a i) * b i) =
      - Finset.univ.sum (fun i : Fin n => a i * b i) := by
  calc
    Finset.univ.sum (fun i : Fin n => (-a i) * b i)
        = Finset.univ.sum (fun i : Fin n => -(a i * b i)) := by
          simp [neg_mul]
    _ = - Finset.univ.sum (fun i : Fin n => a i * b i) := by
          simp

/-- Theorem 1.1: negation does not change the sum of squares. -/
lemma sum_neg_sq_eq_sum_sq (n : ℕ) (a : Fin n → ℝ) :
    Finset.univ.sum (fun i : Fin n => (-a i) ^ (2 : ℕ)) =
      Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

/-- Theorem 1.1: the upper bound for the Cauchy--Schwarz sum. -/
lemma cauchySchwarz_sum_mul_upper (n : ℕ) (a b : Fin n → ℝ) :
    Finset.univ.sum (fun i : Fin n => a i * b i) ≤
      Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
  simpa using
    (Real.sum_mul_le_sqrt_mul_sqrt (s := (Finset.univ : Finset (Fin n))) (f := a) (g := b))

/-- Theorem 1.1: the lower bound for the Cauchy--Schwarz sum. -/
lemma cauchySchwarz_sum_mul_lower (n : ℕ) (a b : Fin n → ℝ) :
    -(Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))) ≤
      Finset.univ.sum (fun i : Fin n => a i * b i) := by
  have h :
      Finset.univ.sum (fun i : Fin n => (-a i) * b i) ≤
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (-a i) ^ (2 : ℕ))) *
          Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
    simpa using
      (Real.sum_mul_le_sqrt_mul_sqrt (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => -a i) (g := b))
  have h' :
      - Finset.univ.sum (fun i : Fin n => a i * b i) ≤
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
          Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
    simpa [sum_neg_mul_eq_neg_sum_mul, sum_neg_sq_eq_sum_sq] using h
  have h'' := neg_le_neg h'
  simpa using h''

/-- Theorem 1.1: absolute-value form of the finite Cauchy--Schwarz inequality. -/
lemma cauchySchwarz_abs_sum_mul (n : ℕ) (a b : Fin n → ℝ) :
    |Finset.univ.sum (fun i : Fin n => a i * b i)| ≤
      Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
  refine (abs_le).2 ?_
  constructor
  · exact cauchySchwarz_sum_mul_lower n a b
  · exact cauchySchwarz_sum_mul_upper n a b

/-- Theorem 1.1 (Cauchy--Schwarz inequality): let `n ≥ 1` and `a b : Fin n → ℝ`. Then
`|∑ i, a i * b i| ≤ (∑ i, (a i)^2)^{1/2} * (∑ i, (b i)^2)^{1/2}`. -/
theorem cauchySchwarz_fin_sum_real (n : ℕ) (hn : 1 ≤ n) (a b : Fin n → ℝ) :
    |Finset.univ.sum (fun i : Fin n => a i * b i)| ≤
      Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
  exact cauchySchwarz_abs_sum_mul n a b

/-- Helper for Theorem 1.2: expand the sum of squares of `a i + b i`. -/
lemma helperForTheorem_1_2_sum_add_sq (n : ℕ) (a b : Fin n → ℝ) :
    Finset.univ.sum (fun i : Fin n => (a i + b i) ^ (2 : ℕ)) =
      Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) +
        Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) +
        2 * Finset.univ.sum (fun i : Fin n => a i * b i) := by
  classical
  calc
    Finset.univ.sum (fun i : Fin n => (a i + b i) ^ (2 : ℕ))
        = Finset.univ.sum (fun i : Fin n =>
            (a i) ^ (2 : ℕ) + (b i) ^ (2 : ℕ) + 2 * (a i * b i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [mul_assoc] using (add_sq' (a i) (b i))
    _ = Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) +
        Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) +
        Finset.univ.sum (fun i : Fin n => 2 * (a i * b i)) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) +
        Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) +
        2 * Finset.univ.sum (fun i : Fin n => a i * b i) := by
          have hmul :
              Finset.univ.sum (fun i : Fin n => 2 * (a i * b i)) =
                2 * Finset.univ.sum (fun i : Fin n => a i * b i) := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
                (a := (2 : ℝ)) (f := fun i : Fin n => a i * b i)).symm
          simp [hmul, add_assoc]

/-- Helper for Theorem 1.2: squared form of the triangle inequality. -/
lemma helperForTheorem_1_2_sum_add_sq_le_rhs_sq (n : ℕ) (a b : Fin n → ℝ) :
    Finset.univ.sum (fun i : Fin n => (a i + b i) ^ (2 : ℕ)) ≤
      (Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) +
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))) ^ (2 : ℕ) := by
  have hsumA_nonneg :
      0 ≤ Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) := by
    exact Finset.sum_nonneg (fun i hi => sq_nonneg (a i))
  have hsumB_nonneg :
      0 ≤ Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) := by
    exact Finset.sum_nonneg (fun i hi => sq_nonneg (b i))
  have hcross :
      Finset.univ.sum (fun i : Fin n => a i * b i) ≤
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
          Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) :=
    cauchySchwarz_sum_mul_upper n a b
  have htwo : 0 ≤ (2 : ℝ) := by
    norm_num
  have hcross2 :
      2 * Finset.univ.sum (fun i : Fin n => a i * b i) ≤
        2 * (Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
          Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))) := by
    exact mul_le_mul_of_nonneg_left hcross htwo
  have hcross2' :
      2 * Finset.univ.sum (fun i : Fin n => a i * b i) ≤
        2 * Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
          Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
    simpa [mul_assoc] using hcross2
  have hsqA :
      (Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)))) ^ (2 : ℕ) =
        Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) := by
    simpa using (Real.sq_sqrt hsumA_nonneg)
  have hsqB :
      (Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))) ^ (2 : ℕ) =
        Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) := by
    simpa using (Real.sq_sqrt hsumB_nonneg)
  have hsq :
      (Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) +
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))) ^ (2 : ℕ) =
        Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) +
          Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) +
          2 * Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
            Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
    calc
      (Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) +
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))) ^ (2 : ℕ)
          = (Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)))) ^ (2 : ℕ) +
            (Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))) ^ (2 : ℕ) +
            2 * Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
              Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
        simpa using
          (add_sq'
            (Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))))
            (Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))))
      _ = Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) +
          Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) +
          2 * Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
            Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
        simp [hsqA, hsqB, add_assoc]
  calc
    Finset.univ.sum (fun i : Fin n => (a i + b i) ^ (2 : ℕ))
        = Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) +
          Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) +
          2 * Finset.univ.sum (fun i : Fin n => a i * b i) :=
        helperForTheorem_1_2_sum_add_sq n a b
    _ ≤ Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) +
          Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)) +
          2 * Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) *
            Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
          have h :=
            add_le_add_left hcross2'
              (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ)) +
                Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))
          simpa [add_assoc] using h
    _ = (Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) +
          Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ)))) ^ (2 : ℕ) := by
          simpa using hsq.symm

/-- Theorem 1.2 (Triangle inequality in `ℝ^n` for the Euclidean norm): let `n ≥ 1` and
`a b : Fin n → ℝ`. Then
`(∑ i, (a i + b i)^2)^{1/2} ≤ (∑ i, (a i)^2)^{1/2} + (∑ i, (b i)^2)^{1/2}`. -/
theorem triangle_inequality_euclidean_norm_fin (n : ℕ) (hn : 1 ≤ n) (a b : Fin n → ℝ) :
    Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i + b i) ^ (2 : ℕ))) ≤
      Real.sqrt (Finset.univ.sum (fun i : Fin n => (a i) ^ (2 : ℕ))) +
        Real.sqrt (Finset.univ.sum (fun i : Fin n => (b i) ^ (2 : ℕ))) := by
  apply (Real.sqrt_le_iff).2
  refine And.intro ?_ ?_
  · exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact helperForTheorem_1_2_sum_add_sq_le_rhs_sq n a b

/-- Definition 1.1 (Convergence of a real sequence from index `m`). -/
def RealSeqConvergesFrom (x : Nat -> Real) (m : Nat) (x0 : Real) : Prop :=
  ∀ ε > 0, ∃ N ≥ m, ∀ n ≥ N, |x0 - x n| ≤ ε

/-- Definition 1.2: the distance function on `ℝ`. -/
abbrev realDist (x y : ℝ) : ℝ := dist x y

/-- Lemma 1.1: a real sequence starting at `m` converges to `x` iff
`lim_{n→∞} d(x_n,x)=0`, where `d(a,b)=|a-b|` is the usual metric on `ℝ`. -/
lemma realSeqConvergesFrom_iff_realDist_tendsto_zero (m : Nat) (x : Nat → Real) (x0 : Real) :
    RealSeqConvergesFrom x m x0 ↔
      RealSeqConvergesFrom (fun n => realDist (x n) x0) m 0 := by
  constructor
  · intro hx ε hε
    rcases hx ε hε with ⟨N, hNm, hN⟩
    refine ⟨N, hNm, ?_⟩
    intro n hn
    have h := hN n hn
    simpa [realDist, Real.dist_eq, abs_sub_comm] using h
  · intro hx ε hε
    rcases hx ε hε with ⟨N, hNm, hN⟩
    refine ⟨N, hNm, ?_⟩
    intro n hn
    have h := hN n hn
    simpa [realDist, Real.dist_eq, abs_sub_comm] using h

/-- Definition 1.3 (Metric space): a metric satisfies the usual axioms. -/
structure TaoMetricAxioms {X : Type*} (d : X → X → ℝ) : Prop where
  eq_zero_iff : ∀ x y, d x y = 0 ↔ x = y
  comm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z
  nonneg : ∀ x y, 0 ≤ d x y

/-- If `d x x = 0` and `d x y = 0 → x = y`, then `d x y = 0 ↔ x = y`. -/
lemma eq_zero_iff_of_self_of_eq_zero_imp {X : Type*} {d : X → X → ℝ}
    (hself : ∀ x, d x x = 0) (himp : ∀ x y, d x y = 0 → x = y) :
    ∀ x y, d x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro hxy
    exact himp x y hxy
  · intro hxy
    subst hxy
    exact hself x

/-- From `d x y = 0 ↔ x = y` we get `d x x = 0`. -/
lemma self_of_eq_zero_iff {X : Type*} {d : X → X → ℝ}
    (hiff : ∀ x y, d x y = 0 ↔ x = y) : ∀ x, d x x = 0 := by
  intro x
  exact (hiff x x).2 rfl

/-- From `d x y = 0 ↔ x = y` we get `d x y = 0 → x = y`. -/
lemma eq_of_eq_zero_of_eq_zero_iff {X : Type*} {d : X → X → ℝ}
    (hiff : ∀ x y, d x y = 0 ↔ x = y) : ∀ x y, d x y = 0 → x = y := by
  intro x y hxy
  exact (hiff x y).1 hxy

/-- Proposition 1.1: the standard zero-distance formulations are equivalent. -/
lemma proposition_1_1 {X : Type*} {d : X → X → ℝ} :
    ((∀ x, d x x = 0) ∧ (∀ x y, d x y = 0 → x = y)) ↔
      (∀ x y, d x y = 0 ↔ x = y) := by
  constructor
  · intro h
    rcases h with ⟨hself, himp⟩
    exact eq_zero_iff_of_self_of_eq_zero_imp hself himp
  · intro h
    refine And.intro ?_ ?_
    · exact self_of_eq_zero_iff h
    · exact eq_of_eq_zero_of_eq_zero_iff h

/-- The distance of a metric space satisfies `TaoMetricAxioms`. -/
lemma metricAxioms_dist {X : Type*} [MetricSpace X] :
    TaoMetricAxioms (fun x y : X => dist x y) := by
  refine
    { eq_zero_iff := ?_
      comm := ?_
      triangle := ?_
      nonneg := ?_ }
  · intro x y
    simp
  · intro x y
    simpa using (dist_comm x y)
  · intro x y z
    simpa using (dist_triangle x y z)
  · intro x y
    simp

/-- The real distance satisfies `TaoMetricAxioms`. -/
lemma metricAxioms_realDist : TaoMetricAxioms (fun x y : ℝ => realDist x y) := by
  simpa [realDist] using (metricAxioms_dist (X := ℝ))

/-- A metric satisfies `d x x = 0`. -/
lemma TaoMetricAxioms.self {X : Type*} {d : X → X → ℝ} (h : TaoMetricAxioms d) (x : X) :
    d x x = 0 := by
  exact (h.eq_zero_iff x x).2 rfl

/-- The real distance equals the absolute value of the difference. -/
lemma realDist_eq_abs_sub (x y : ℝ) : realDist x y = |x - y| := by
  simpa [realDist] using (Real.dist_eq x y)

/-- The absolute value of a difference equals the real distance. -/
lemma abs_sub_eq_realDist (x y : ℝ) : |x - y| = realDist x y := by
  exact (realDist_eq_abs_sub x y).symm

/-- Definition 1.4 (Standard metric on `ℝ`). -/
def standardMetric (x y : ℝ) : ℝ := |x - y|

/-- The standard metric agrees with `realDist` on `ℝ`. -/
lemma standardMetric_eq_realDist (x y : ℝ) : standardMetric x y = realDist x y := by
  simp [standardMetric, abs_sub_eq_realDist]

/-- The standard metric on `ℝ` satisfies `TaoMetricAxioms`. -/
lemma metricAxioms_standardMetric : TaoMetricAxioms (fun x y : ℝ => standardMetric x y) := by
  simpa [standardMetric_eq_realDist] using (metricAxioms_realDist)

/-- Definition 1.5: for a metric space `(X, d)` and `Y ⊆ X`, the induced metric on `Y` is the restriction `d|_{Y×Y}` given by `d|_{Y×Y}(y1, y2) = d(y1, y2)`; the subspace induced by `Y` is the metric space `(Y, d|_{Y×Y})`. -/
def inducedMetric {X : Type*} [MetricSpace X] (Y : Set X) :
    Subtype Y → Subtype Y → ℝ :=
  fun y1 y2 => dist (y1 : X) (y2 : X)

/-- The metric space structure on a subset induced by the ambient metric. -/
abbrev subspaceMetricSpace {X : Type*} [MetricSpace X] (Y : Set X) :
    MetricSpace (Subtype Y) :=
  inferInstance

/-- Definition 1.6: for `n ≥ 1`, the Euclidean (ℓ^2) metric on `ℝ^n` is `d_{ℓ^2}(x,y) = √(∑ i, (x i - y i)^2)`; the metric space `(ℝ^n, d_{ℓ^2})` is called Euclidean space of dimension `n`. -/
noncomputable abbrev euclideanMetric (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ :=
  dist

/-- Definition 1.7: for `n ≥ 1`, the taxicab (ℓ^1) metric on `ℝ^n` is
`d_{ℓ^1}(x,y) = ∑ i, |x i - y i|`, where `x = (x_1, ..., x_n)` and
`y = (y_1, ..., y_n)`. -/
def taxicabMetric (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun i => |x i - y i|)

/-- The ℓ^2 distance on `ℝ^n` given by `sqrt (∑ i, |x i - y i|^2)`. -/
noncomputable def l2Distance (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (Finset.univ.sum (fun i => |x i - y i| ^ (2 : ℕ)))

/-- Proposition 1.2: the sum of squares of `|x i - y i|` is bounded by the square of the sum. -/
lemma sum_abs_sub_sq_le_sq_sum_abs_sub (n : ℕ) (x y : Fin n → ℝ) :
    (Finset.univ.sum (fun i => |x i - y i| ^ (2 : ℕ))) ≤
      (Finset.univ.sum (fun i => |x i - y i|)) ^ (2 : ℕ) := by
  classical
  have hnonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |x i - y i| := by
    intro i hi
    exact abs_nonneg (x i - y i)
  simpa using
    (Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => |x i - y i|) hnonneg)

/-- Proposition 1.2: the ℓ² distance is bounded above by the ℓ¹ distance. -/
lemma l2Distance_le_taxicabMetric (n : ℕ) (x y : Fin n → ℝ) :
    l2Distance n x y ≤ taxicabMetric n x y := by
  unfold l2Distance taxicabMetric
  apply (Real.sqrt_le_iff).2
  refine And.intro ?_ ?_
  · exact Finset.sum_nonneg (fun i hi => abs_nonneg (x i - y i))
  · exact sum_abs_sub_sq_le_sq_sum_abs_sub n x y

/-- Proposition 1.2: the ℓ¹ distance is bounded by `√n` times the ℓ² distance. -/
lemma taxicabMetric_le_sqrt_n_mul_l2Distance (n : ℕ) (x y : Fin n → ℝ) :
    taxicabMetric n x y ≤ Real.sqrt (n : ℝ) * l2Distance n x y := by
  classical
  have h :=
    (Real.sum_mul_le_sqrt_mul_sqrt (s := Finset.univ)
      (f := fun i : Fin n => |x i - y i|)
      (g := fun _ : Fin n => (1 : ℝ)))
  simpa [taxicabMetric, l2Distance, mul_comm, mul_left_comm, mul_assoc] using h

/-- Proposition 1.2: Let `n ≥ 1` and `x,y ∈ ℝ^n`. Define
`d_{ℓ^1}(x,y) = ∑ i, |x i - y i|` and
`d_{ℓ^2}(x,y) = (∑ i, |x i - y i|^2)^{1/2}`. Then
`d_{ℓ^2}(x,y) ≤ d_{ℓ^1}(x,y) ≤ √n * d_{ℓ^2}(x,y)`. -/
theorem l2Distance_le_l1Distance_le_sqrt_n_l2Distance
    (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → ℝ) :
    l2Distance n x y ≤ taxicabMetric n x y ∧
      taxicabMetric n x y ≤ Real.sqrt (n : ℝ) * l2Distance n x y := by
  constructor
  · exact l2Distance_le_taxicabMetric n x y
  · exact taxicabMetric_le_sqrt_n_mul_l2Distance n x y

/-- Definition 1.8: for `n ≥ 1`, the sup norm (ℓ^∞) metric on `ℝ^n` is
`d_{ℓ^∞}(x,y) = sup { |x i - y i| : 1 ≤ i ≤ n }`, where `x = (x_1, ..., x_n)` and
`y = (y_1, ..., y_n)`. -/
noncomputable def supNormMetric (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  sSup (Set.range (fun i : Fin n => |x i - y i|))

/-- Proposition 1.3: the range of coordinate differences is nonempty when `n ≥ 1`. -/
lemma prop_1_3_range_abs_sub_nonempty (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → ℝ) :
    (Set.range (fun i : Fin n => |x i - y i|)).Nonempty := by
  have h0 : (0 : ℕ) < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  refine ⟨|x ⟨0, h0⟩ - y ⟨0, h0⟩|, ?_⟩
  exact ⟨⟨0, h0⟩, rfl⟩

/-- Proposition 1.3: the range of coordinate differences is bounded above. -/
lemma prop_1_3_bddAbove_range_abs_sub (n : ℕ) (x y : Fin n → ℝ) :
    BddAbove (Set.range (fun i : Fin n => |x i - y i|)) := by
  classical
  simp

/-- Proposition 1.3: each coordinate difference is bounded by the sup norm metric. -/
lemma prop_1_3_abs_sub_le_supNormMetric (n : ℕ) (x y : Fin n → ℝ) :
    ∀ i : Fin n, |x i - y i| ≤ supNormMetric n x y := by
  intro i
  unfold supNormMetric
  have hbdd : BddAbove (Set.range (fun i : Fin n => |x i - y i|)) :=
    prop_1_3_bddAbove_range_abs_sub n x y
  exact le_csSup hbdd ⟨i, rfl⟩

/-- Proposition 1.3: the sup norm metric is nonnegative. -/
lemma prop_1_3_supNormMetric_nonneg (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → ℝ) :
    0 ≤ supNormMetric n x y := by
  have h0 : (0 : ℕ) < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hle :
      |x ⟨0, h0⟩ - y ⟨0, h0⟩| ≤ supNormMetric n x y :=
    prop_1_3_abs_sub_le_supNormMetric n x y ⟨0, h0⟩
  exact le_trans (abs_nonneg (x ⟨0, h0⟩ - y ⟨0, h0⟩)) hle

/-- Proposition 1.3: each coordinate difference is bounded by the ℓ² distance. -/
lemma prop_1_3_abs_sub_le_l2Distance (n : ℕ) (x y : Fin n → ℝ) :
    ∀ i : Fin n, |x i - y i| ≤ l2Distance n x y := by
  intro i
  unfold l2Distance
  apply Real.le_sqrt_of_sq_le
  apply Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j : Fin n => |x j - y j| ^ (2 : ℕ))
  · intro j hj
    exact sq_nonneg (|x j - y j|)
  · exact Finset.mem_univ i

/-- Proposition 1.3: the ℓ² distance is bounded by `√n` times the sup norm metric. -/
lemma prop_1_3_l2Distance_le_sqrt_n_mul_supNormMetric
    (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → ℝ) :
    l2Distance n x y ≤ Real.sqrt (n : ℝ) * supNormMetric n x y := by
  classical
  have hs : 0 ≤ supNormMetric n x y := prop_1_3_supNormMetric_nonneg n hn x y
  unfold l2Distance
  apply (Real.sqrt_le_iff).2
  refine And.intro ?_ ?_
  · exact mul_nonneg (Real.sqrt_nonneg _) hs
  · have hpoint : ∀ i : Fin n,
        |x i - y i| ^ (2 : ℕ) ≤ (supNormMetric n x y) ^ (2 : ℕ) := by
      intro i
      have hle : |x i - y i| ≤ supNormMetric n x y :=
        prop_1_3_abs_sub_le_supNormMetric n x y i
      have hmul :
          |x i - y i| * |x i - y i| ≤
            supNormMetric n x y * supNormMetric n x y :=
        mul_le_mul hle hle (abs_nonneg (x i - y i)) hs
      simpa [pow_two] using hmul
    have hsum :
        Finset.univ.sum (fun i : Fin n => |x i - y i| ^ (2 : ℕ)) ≤
          Finset.univ.sum (fun _ : Fin n => (supNormMetric n x y) ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hpoint i
    have hsum' :
        Finset.univ.sum (fun _ : Fin n => (supNormMetric n x y) ^ (2 : ℕ)) =
          (n : ℝ) * (supNormMetric n x y) ^ (2 : ℕ) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsqrt_sq :
        (Real.sqrt (n : ℝ) * supNormMetric n x y) ^ (2 : ℕ) =
          (n : ℝ) * (supNormMetric n x y) ^ (2 : ℕ) := by
      calc
        (Real.sqrt (n : ℝ) * supNormMetric n x y) ^ (2 : ℕ) =
            (Real.sqrt (n : ℝ) ^ (2 : ℕ)) *
              (supNormMetric n x y) ^ (2 : ℕ) := by
          simp [mul_pow]
        _ = (n : ℝ) * (supNormMetric n x y) ^ (2 : ℕ) := by
          simp [Real.sq_sqrt hnnonneg]
    calc
      Finset.univ.sum (fun i : Fin n => |x i - y i| ^ (2 : ℕ)) ≤
          (n : ℝ) * (supNormMetric n x y) ^ (2 : ℕ) := by
        calc
          Finset.univ.sum (fun i : Fin n => |x i - y i| ^ (2 : ℕ)) ≤
              Finset.univ.sum (fun _ : Fin n => (supNormMetric n x y) ^ (2 : ℕ)) := hsum
          _ = (n : ℝ) * (supNormMetric n x y) ^ (2 : ℕ) := hsum'
      _ = (Real.sqrt (n : ℝ) * supNormMetric n x y) ^ (2 : ℕ) := by
        symm
        exact hsqrt_sq

/-- Proposition 1.3: Let `n ≥ 1`. For all `x,y ∈ ℝ^n`, the metrics
`d_{ℓ^∞}` and `d_{ℓ^2}` satisfy `(1/√n) d_{ℓ^2}(x,y) ≤ d_{ℓ^∞}(x,y) ≤ d_{ℓ^2}(x,y)`.
Equivalently, for all `v ∈ ℝ^n`, `(1/√n) ‖v‖_2 ≤ ‖v‖_∞ ≤ ‖v‖_2`. -/
theorem one_div_sqrt_n_l2Distance_le_supNormMetric_le_l2Distance
    (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → ℝ) :
    (1 / Real.sqrt (n : ℝ)) * l2Distance n x y ≤ supNormMetric n x y ∧
      supNormMetric n x y ≤ l2Distance n x y := by
  classical
  constructor
  · have hmain :
        l2Distance n x y ≤ Real.sqrt (n : ℝ) * supNormMetric n x y :=
      prop_1_3_l2Distance_le_sqrt_n_mul_supNormMetric n hn x y
    have hnpos : 0 < (n : ℝ) :=
      (Nat.cast_pos).2 (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := (Real.sqrt_pos).2 hnpos
    have hdiv :
        l2Distance n x y / Real.sqrt (n : ℝ) ≤ supNormMetric n x y := by
      apply (div_le_iff₀' hsqrt_pos).2
      exact hmain
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv
  · unfold supNormMetric
    have hnonempty :
        (Set.range (fun i : Fin n => |x i - y i|)).Nonempty :=
      prop_1_3_range_abs_sub_nonempty n hn x y
    apply csSup_le hnonempty
    intro b hb
    rcases hb with ⟨i, rfl⟩
    exact prop_1_3_abs_sub_le_l2Distance n x y i

/-- Definition 1.9 (Convergence of sequences in metric spaces): a sequence
`(x^{(n)})_{n=m}^∞` in a metric space converges to `x` if for every `ε > 0`
there exists an integer `N ≥ m` such that `dist (x n) x ≤ ε` for all `n ≥ N`
(equivalently, `dist (x n) x → 0` as `n → ∞`). -/
def MetricSeqConvergesFrom {X : Type*} [MetricSpace X]
    (x : ℤ → X) (m : ℤ) (x0 : X) : Prop :=
  ∀ ε > 0, ∃ N ≥ m, ∀ n ≥ N, dist (x n) x0 ≤ ε

/-- Proposition 1.4: if a sequence in a metric space converges to `x0` from index `m`,
then any tail starting at `m' ≥ m` also converges to `x0`. -/
theorem tail_converges_of_converges {X : Type*} [MetricSpace X]
    (x : ℤ → X) (m : ℤ) (x0 : X) :
    MetricSeqConvergesFrom x m x0 → ∀ m' ≥ m, MetricSeqConvergesFrom x m' x0 := by
  intro h m' hm'
  unfold MetricSeqConvergesFrom at h ⊢
  intro ε hε
  rcases h ε hε with ⟨N, hNm, hbound⟩
  refine ⟨max N m', ?_, ?_⟩
  · exact le_max_right N m'
  · intro n hn
    have hN : N ≤ n := le_trans (le_max_left N m') hn
    exact hbound n hN

/-- Convergence from index `m` with respect to a specified distance function. -/
def SeqConvergesFromWith {X : Type*} (d : X → X → ℝ)
    (x : ℕ → X) (m : ℕ) (x0 : X) : Prop :=
  ∀ ε > 0, ∃ N ≥ m, ∀ n ≥ N, d (x n) x0 ≤ ε

/-- Proposition 1.5: transfer convergence when one distance is pointwise bounded by another. -/
lemma seqConvergesFromWith_of_le {X : Type*} {d1 d2 : X → X → ℝ}
    {x : ℕ → X} {m : ℕ} {x0 : X} (h : ∀ u v, d1 u v ≤ d2 u v) :
    SeqConvergesFromWith d2 x m x0 → SeqConvergesFromWith d1 x m x0 := by
  intro hconv
  unfold SeqConvergesFromWith at hconv ⊢
  intro ε hε
  rcases hconv ε hε with ⟨N, hNm, hbound⟩
  refine ⟨N, hNm, ?_⟩
  intro n hn
  have hle : d1 (x n) x0 ≤ d2 (x n) x0 := h (x n) x0
  exact le_trans hle (hbound n hn)

/-- Proposition 1.5: transfer convergence under a pointwise bound by a positive multiple. -/
lemma seqConvergesFromWith_of_le_mul {X : Type*} {d1 d2 : X → X → ℝ}
    {x : ℕ → X} {m : ℕ} {x0 : X} {C : ℝ} (hC : 0 < C)
    (h : ∀ u v, d1 u v ≤ C * d2 u v) :
    SeqConvergesFromWith d2 x m x0 → SeqConvergesFromWith d1 x m x0 := by
  intro hconv
  unfold SeqConvergesFromWith at hconv ⊢
  intro ε hε
  have hε' : 0 < ε / C := div_pos hε hC
  rcases hconv (ε / C) hε' with ⟨N, hNm, hbound⟩
  refine ⟨N, hNm, ?_⟩
  intro n hn
  have hle : d1 (x n) x0 ≤ C * d2 (x n) x0 := h (x n) x0
  have hle' : C * d2 (x n) x0 ≤ C * (ε / C) := by
    exact mul_le_mul_of_nonneg_left (hbound n hn) (le_of_lt hC)
  have hCne : (C : ℝ) ≠ 0 := ne_of_gt hC
  have hCeq : C * (ε / C) = ε := by
    calc
      C * (ε / C) = C * ε / C := by
        exact (mul_div_assoc' C ε C)
      _ = ε := by
        exact mul_div_cancel_left₀ ε hCne
  calc
    d1 (x n) x0 ≤ C * d2 (x n) x0 := hle
    _ ≤ C * (ε / C) := hle'
    _ = ε := hCeq

/-- Proposition 1.5: a uniform index for finitely many coordinate bounds. -/
lemma exists_uniform_index_forall_fin (n : ℕ) (m : ℕ) {P : Fin n → ℕ → Prop}
    (h : ∀ j : Fin n, ∃ Nj ≥ m, ∀ k ≥ Nj, P j k) :
    ∃ N ≥ m, ∀ k ≥ N, ∀ j : Fin n, P j k := by
  classical
  cases n with
  | zero =>
      refine ⟨m, le_rfl, ?_⟩
      intro k hk j
      exact (Fin.elim0 j)
  | succ n' =>
      let Nfun : Fin (Nat.succ n') → ℕ := fun j => Classical.choose (h j)
      have hNfun_m : ∀ j, m ≤ Nfun j := by
        intro j
        exact (Classical.choose_spec (h j)).1
      have hNfun_prop : ∀ j, ∀ k ≥ Nfun j, P j k := by
        intro j
        exact (Classical.choose_spec (h j)).2
      let N : ℕ := (Finset.univ : Finset (Fin (Nat.succ n'))).sup Nfun
      have hN_le : ∀ j, Nfun j ≤ N := by
        intro j
        have hj : j ∈ (Finset.univ : Finset (Fin (Nat.succ n'))) := Finset.mem_univ j
        exact
          Finset.le_sup (s := (Finset.univ : Finset (Fin (Nat.succ n')))) (f := Nfun) hj
      have hNm : m ≤ N := by
        have j0 : Fin (Nat.succ n') := ⟨0, Nat.succ_pos n'⟩
        exact le_trans (hNfun_m j0) (hN_le j0)
      refine ⟨N, hNm, ?_⟩
      intro k hk j
      have hk' : Nfun j ≤ k := le_trans (hN_le j) hk
      exact hNfun_prop j k hk'

/-- Proposition 1.5 (Equivalence of `ℓ^1`, `ℓ^2`, `ℓ^∞` convergence in `ℝ^n`):
let `n ∈ ℕ`, let `(x^{(k)})_{k=m}^∞` be a sequence in `ℝ^n` with
`x^{(k)} = (x_1^{(k)}, ..., x_n^{(k)})`, and let `x = (x_1, ..., x_n)`.
Then the following are equivalent: (a) `x^{(k)} → x` with respect to `d_{ℓ^2}`,
(b) `x^{(k)} → x` with respect to `d_{ℓ^1}`, (c) `x^{(k)} → x` with respect to
`d_{ℓ^∞}`, and (d) for every `1 ≤ j ≤ n`, the real sequence `(x_j^{(k)})_{k=m}^∞`
converges to `x_j`. -/
theorem equiv_l1_l2_linf_convergence_Rn
    (n : ℕ) (m : ℕ) (x : ℕ → Fin n → ℝ) (x0 : Fin n → ℝ) :
    (SeqConvergesFromWith (l2Distance n) x m x0 ↔
      SeqConvergesFromWith (taxicabMetric n) x m x0) ∧
    (SeqConvergesFromWith (taxicabMetric n) x m x0 ↔
      SeqConvergesFromWith (supNormMetric n) x m x0) ∧
    (SeqConvergesFromWith (supNormMetric n) x m x0 ↔
      ∀ j : Fin n, RealSeqConvergesFrom (fun k => x k j) m (x0 j)) := by
  cases n with
  | zero =>
      have h_l2 : SeqConvergesFromWith (l2Distance 0) x m x0 := by
        unfold SeqConvergesFromWith
        intro ε hε
        refine ⟨m, le_rfl, ?_⟩
        intro n hn
        have hε' : 0 ≤ ε := le_of_lt hε
        simpa [l2Distance] using hε'
      have h_l1 : SeqConvergesFromWith (taxicabMetric 0) x m x0 := by
        unfold SeqConvergesFromWith
        intro ε hε
        refine ⟨m, le_rfl, ?_⟩
        intro n hn
        have hε' : 0 ≤ ε := le_of_lt hε
        simpa [taxicabMetric] using hε'
      have h_linf : SeqConvergesFromWith (supNormMetric 0) x m x0 := by
        unfold SeqConvergesFromWith
        intro ε hε
        refine ⟨m, le_rfl, ?_⟩
        intro n hn
        have hε' : 0 ≤ ε := le_of_lt hε
        simpa [supNormMetric] using hε'
      have h_coord :
          ∀ j : Fin 0, RealSeqConvergesFrom (fun k => x k j) m (x0 j) := by
        intro j
        exact (Fin.elim0 j)
      refine And.intro ?_ ?_
      · constructor
        · intro h
          exact h_l1
        · intro h
          exact h_l2
      · refine And.intro ?_ ?_
        · constructor
          · intro h
            exact h_linf
          · intro h
            exact h_l1
        · constructor
          · intro h
            exact h_coord
          · intro h
            exact h_linf
  | succ n' =>
      have hn : 1 ≤ Nat.succ n' := Nat.succ_le_succ (Nat.zero_le n')
      have hnpos : 0 < (Nat.succ n' : ℝ) := (Nat.cast_pos).2 (Nat.succ_pos n')
      have hsqrt_pos : 0 < Real.sqrt (Nat.succ n' : ℝ) := (Real.sqrt_pos).2 hnpos
      have h_l2_l1 :
          SeqConvergesFromWith (l2Distance (Nat.succ n')) x m x0 ↔
            SeqConvergesFromWith (taxicabMetric (Nat.succ n')) x m x0 := by
        constructor
        · intro h2
          have hle :
              ∀ u v, taxicabMetric (Nat.succ n') u v ≤
                Real.sqrt (Nat.succ n' : ℝ) * l2Distance (Nat.succ n') u v :=
            taxicabMetric_le_sqrt_n_mul_l2Distance (Nat.succ n')
          exact
            seqConvergesFromWith_of_le_mul (C := Real.sqrt (Nat.succ n' : ℝ)) hsqrt_pos hle h2
        · intro h1
          have hle :
              ∀ u v, l2Distance (Nat.succ n') u v ≤
                taxicabMetric (Nat.succ n') u v :=
            l2Distance_le_taxicabMetric (Nat.succ n')
          exact seqConvergesFromWith_of_le hle h1
      have h_l2_linf :
          SeqConvergesFromWith (l2Distance (Nat.succ n')) x m x0 ↔
            SeqConvergesFromWith (supNormMetric (Nat.succ n')) x m x0 := by
        constructor
        · intro h2
          have hle :
              ∀ u v, supNormMetric (Nat.succ n') u v ≤
                l2Distance (Nat.succ n') u v := by
            intro u v
            exact
              (one_div_sqrt_n_l2Distance_le_supNormMetric_le_l2Distance
                (Nat.succ n') hn u v).2
          exact seqConvergesFromWith_of_le hle h2
        · intro hsup
          have hle :
              ∀ u v, l2Distance (Nat.succ n') u v ≤
                Real.sqrt (Nat.succ n' : ℝ) * supNormMetric (Nat.succ n') u v := by
            intro u v
            exact prop_1_3_l2Distance_le_sqrt_n_mul_supNormMetric (Nat.succ n') hn u v
          exact
            seqConvergesFromWith_of_le_mul (C := Real.sqrt (Nat.succ n' : ℝ)) hsqrt_pos hle hsup
      have h_l1_linf :
          SeqConvergesFromWith (taxicabMetric (Nat.succ n')) x m x0 ↔
            SeqConvergesFromWith (supNormMetric (Nat.succ n')) x m x0 := by
        constructor
        · intro h1
          have h2 : SeqConvergesFromWith (l2Distance (Nat.succ n')) x m x0 :=
            h_l2_l1.mpr h1
          exact h_l2_linf.mp h2
        · intro hsup
          have h2 : SeqConvergesFromWith (l2Distance (Nat.succ n')) x m x0 :=
            h_l2_linf.mpr hsup
          exact h_l2_l1.mp h2
      have h_linf_coord :
          SeqConvergesFromWith (supNormMetric (Nat.succ n')) x m x0 ↔
            ∀ j : Fin (Nat.succ n'), RealSeqConvergesFrom (fun k => x k j) m (x0 j) := by
        constructor
        · intro hsup j
          unfold RealSeqConvergesFrom
          intro ε hε
          rcases hsup ε hε with ⟨N, hNm, hbound⟩
          refine ⟨N, hNm, ?_⟩
          intro n hn
          have hle :
              |x n j - x0 j| ≤ supNormMetric (Nat.succ n') (x n) x0 :=
            prop_1_3_abs_sub_le_supNormMetric (Nat.succ n') (x n) x0 j
          have hle' :
              |x0 j - x n j| ≤ supNormMetric (Nat.succ n') (x n) x0 := by
            simpa [abs_sub_comm] using hle
          exact le_trans hle' (hbound n hn)
        · intro hcoord
          unfold SeqConvergesFromWith
          intro ε hε
          have hcoord' :
              ∀ j : Fin (Nat.succ n'), ∃ Nj ≥ m, ∀ k ≥ Nj, |x0 j - x k j| ≤ ε := by
            intro j
            have hj := hcoord j
            unfold RealSeqConvergesFrom at hj
            exact hj ε hε
          rcases
            exists_uniform_index_forall_fin (n := Nat.succ n') (m := m)
              (P := fun j k => |x0 j - x k j| ≤ ε) hcoord' with ⟨N, hNm, hbound⟩
          refine ⟨N, hNm, ?_⟩
          intro k hk
          have hnonempty :
              (Set.range (fun i : Fin (Nat.succ n') => |x k i - x0 i|)).Nonempty :=
            prop_1_3_range_abs_sub_nonempty (Nat.succ n') hn (x k) x0
          have hbound' : ∀ i : Fin (Nat.succ n'), |x k i - x0 i| ≤ ε := by
            intro i
            have hki : |x0 i - x k i| ≤ ε := hbound k hk i
            simpa [abs_sub_comm] using hki
          unfold supNormMetric
          apply csSup_le hnonempty
          intro b hb
          rcases hb with ⟨i, rfl⟩
          exact hbound' i
      refine And.intro h_l2_l1 ?_
      refine And.intro h_l1_linf h_linf_coord

/-- The discrete metric on a type: `d(a,b)=0` if `a=b` and `d(a,b)=1` otherwise. -/
noncomputable def discreteMetric {X : Type*} (a b : X) : ℝ :=
  @ite ℝ (a = b) (Classical.decEq (α := X) a b) 0 1

/-- Proposition 1.6: in the discrete metric, the bound `≤ 1/2` forces equality. -/
lemma discreteMetric_le_one_half_iff_eq {X : Type*} (a b : X) :
    discreteMetric (X := X) a b ≤ (1 / 2 : ℝ) ↔ a = b := by
  classical
  by_cases h : a = b
  · subst h
    simp [discreteMetric]
  · constructor
    · intro hle
      have hle' : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
        simpa [discreteMetric, h] using hle
      have hlt : (1 / 2 : ℝ) < (1 : ℝ) := by
        nlinarith
      exact (False.elim ((not_le_of_gt hlt) hle'))
    · intro hEq
      exact (h hEq).elim

/-- Proposition 1.6: convergence in the discrete metric implies eventual equality. -/
lemma discreteMetric_eventually_eq_of_converges {X : Type*} (x : ℕ → X) (m : ℕ) (x0 : X) :
    SeqConvergesFromWith (discreteMetric (X := X)) x m x0 →
      ∃ N ≥ m, ∀ n ≥ N, x n = x0 := by
  intro hconv
  unfold SeqConvergesFromWith at hconv
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) := by
    nlinarith
  rcases hconv (1 / 2 : ℝ) hpos with ⟨N, hNm, hbound⟩
  refine ⟨N, hNm, ?_⟩
  intro n hn
  have hle : discreteMetric (X := X) (x n) x0 ≤ (1 / 2 : ℝ) := hbound n hn
  exact (discreteMetric_le_one_half_iff_eq (a := x n) (b := x0)).1 hle

/-- Proposition 1.6: eventual equality implies convergence in the discrete metric. -/
lemma discreteMetric_converges_of_eventually_eq {X : Type*} (x : ℕ → X) (m : ℕ) (x0 : X) :
    (∃ N ≥ m, ∀ n ≥ N, x n = x0) →
      SeqConvergesFromWith (discreteMetric (X := X)) x m x0 := by
  intro h
  rcases h with ⟨N, hNm, hEq⟩
  unfold SeqConvergesFromWith
  intro ε hε
  refine ⟨N, hNm, ?_⟩
  intro n hn
  have hx : x n = x0 := hEq n hn
  have hle : (0 : ℝ) ≤ ε := le_of_lt hε
  simpa [discreteMetric, hx] using hle

/-- Proposition 1.6 (Convergence in the discrete metric): a sequence converges to `x0` with
respect to the discrete metric iff it is eventually constantly equal to `x0`. -/
theorem discreteMetric_converges_iff_eventually_eq {X : Type*}
    (x : ℕ → X) (m : ℕ) (x0 : X) :
    SeqConvergesFromWith (discreteMetric (X := X)) x m x0 ↔
      ∃ N ≥ m, ∀ n ≥ N, x n = x0 := by
  constructor
  · exact discreteMetric_eventually_eq_of_converges x m x0
  · exact discreteMetric_converges_of_eventually_eq x m x0

/-- Proposition 1.7 (Uniqueness of limits): if a sequence converges to `x0` and also to `x1`
with respect to a metric `d`, then `x0 = x1`. -/
theorem metric_limit_unique {X : Type*} [MetricSpace X]
    (x : ℕ → X) (m : ℕ) (x0 x1 : X) :
    SeqConvergesFromWith (d := dist) x m x0 →
      SeqConvergesFromWith (d := dist) x m x1 →
      x0 = x1 := by
  intro hx0 hx1
  by_contra hne
  have hdist : 0 < dist x0 x1 := (dist_pos).2 hne
  have h3 : (0 : ℝ) < 3 := by
    nlinarith
  have hε : 0 < dist x0 x1 / 3 := div_pos hdist h3
  unfold SeqConvergesFromWith at hx0 hx1
  rcases hx0 (dist x0 x1 / 3) hε with ⟨N0, hN0m, h0⟩
  rcases hx1 (dist x0 x1 / 3) hε with ⟨N1, hN1m, h1⟩
  have h0' : dist (x (max N0 N1)) x0 ≤ dist x0 x1 / 3 :=
    h0 (max N0 N1) (le_max_left N0 N1)
  have h1' : dist (x (max N0 N1)) x1 ≤ dist x0 x1 / 3 :=
    h1 (max N0 N1) (le_max_right N0 N1)
  have h0'' : dist x0 (x (max N0 N1)) ≤ dist x0 x1 / 3 := by
    simpa [dist_comm] using h0'
  have htriangle :
      dist x0 x1 ≤ dist x0 (x (max N0 N1)) + dist (x (max N0 N1)) x1 :=
    dist_triangle x0 (x (max N0 N1)) x1
  have hle : dist x0 x1 ≤ dist x0 x1 / 3 + dist x0 x1 / 3 := by
    exact le_trans htriangle (add_le_add h0'' h1')
  have hlt : dist x0 x1 / 3 + dist x0 x1 / 3 < dist x0 x1 := by
    nlinarith [hdist]
  have hcontr : dist x0 x1 < dist x0 x1 := lt_of_le_of_lt hle hlt
  exact (lt_irrefl _ hcontr)

/-- Proposition 1.8: Let `(X, d)` be a metric space and let `f : X → X` be a
bijection. Define `d'(x,y) = d (f x) (f y)`. Then `d'` is a metric on `X`. -/
theorem metricAxioms_comp_bijective {X : Type*} {d : X → X → ℝ}
    (hd : TaoMetricAxioms d) {f : X → X} (hf : Function.Bijective f) :
    TaoMetricAxioms (fun x y => d (f x) (f y)) := by
  refine
    { eq_zero_iff := ?_
      comm := ?_
      triangle := ?_
      nonneg := ?_ }
  · intro x y
    constructor
    · intro hxy
      have hfx : f x = f y := (hd.eq_zero_iff (f x) (f y)).1 hxy
      exact (hf.1 hfx)
    · intro hxy
      have hfx : f x = f y := congrArg f hxy
      exact (hd.eq_zero_iff (f x) (f y)).2 hfx
  · intro x y
    simpa using (hd.comm (f x) (f y))
  · intro x y z
    simpa using (hd.triangle (f x) (f y) (f z))
  · intro x y
    simpa using (hd.nonneg (f x) (f y))

/-- Proposition 1.9 (prop:1.9): `0` and `1` lie in the closed unit interval. -/
lemma zero_mem_Icc_zero_one_and_one_mem_Icc_zero_one :
    (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩

/-- Proposition 1.9 (prop:1.9): the map on the closed unit interval that sends
`0` to `1`, `1` to `0`, and fixes every `x ∈ (0,1)`. -/
noncomputable def swapEndpointsOnUnitInterval :
    {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} → {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
  fun x =>
    if _ : (x : ℝ) = 0 then
      ⟨1, (zero_mem_Icc_zero_one_and_one_mem_Icc_zero_one).2⟩
    else if _ : (x : ℝ) = 1 then
      ⟨0, (zero_mem_Icc_zero_one_and_one_mem_Icc_zero_one).1⟩
    else
      x

/-- Proposition 1.9 (prop:1.9): the metric `d'(x,y)=|f(x)-f(y)|` on the closed
unit interval induced by `swapEndpointsOnUnitInterval`. -/
noncomputable def swapEndpointsMetric
    (x y : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ :=
  |(swapEndpointsOnUnitInterval x : ℝ) - (swapEndpointsOnUnitInterval y : ℝ)|

/-- Proposition 1.9 (prop:1.9): `1/n` lies in `[0,1]` for positive `n`. -/
lemma one_div_mem_Icc_zero_one_of_nat_pos (n : ℕ) (hn : n ≠ 0) :
    ((1 : ℝ) / (n : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hpos_real : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hpos_nat
  have hle_nat : (1 : ℕ) ≤ n := Nat.succ_le_iff.mpr hpos_nat
  have hle_real : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hle_nat
  have hnonneg : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by
    exact one_div_nonneg.mpr (le_of_lt hpos_real)
  have hle_one : (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) := by
    exact (div_le_one hpos_real).2 hle_real
  exact ⟨hnonneg, hle_one⟩


end Section01
end Chap01
