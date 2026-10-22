/-
Authors: Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/Analysis2_Tao_2022/README.md (Contributors).
-/

import Mathlib

section Chap02
section Section02

open Filter

/-- Definition 2.2: Pairing of functions. For functions `f : X → Y` and
`g : X → Z`, the pairing `(f,g)` is the function `X → Y × Z` given by
`x ↦ (f x, g x)`. -/
def pairing {X Y Z : Type*} (f : X → Y) (g : X → Z) : X → Y × Z :=
  fun x => (f x, g x)

/-- Lemma 2.1: For functions `f, g : X → ℝ` and their direct sum
`(f, g) : X → ℝ × ℝ` with the Euclidean metric: (a) for any `x0`, `f` and `g`
are both continuous at `x0` iff `(f, g)` is continuous at `x0`; (b) `f` and
`g` are both continuous iff `(f, g)` is continuous. -/
lemma continuousAt_and_continuous_pairing_iff {X : Type*} [TopologicalSpace X]
    (f g : X → ℝ) :
    (∀ x0 : X, (ContinuousAt f x0 ∧ ContinuousAt g x0) ↔
        ContinuousAt (pairing f g) x0) ∧
      ((Continuous f ∧ Continuous g) ↔ Continuous (pairing f g)) := by
  constructor
  · intro x0
    constructor
    · intro h
      rcases h with ⟨hf, hg⟩
      change ContinuousAt (fun x : X => (f x, g x)) x0
      exact ContinuousAt.prodMk hf hg
    · intro hpair
      have hf : ContinuousAt (fun x : X => (pairing f g x).1) x0 :=
        ContinuousAt.fst hpair
      have hg : ContinuousAt (fun x : X => (pairing f g x).2) x0 :=
        ContinuousAt.snd hpair
      have hf' : ContinuousAt f x0 := by
        simpa [pairing] using hf
      have hg' : ContinuousAt g x0 := by
        simpa [pairing] using hg
      exact And.intro hf' hg'
  · constructor
    · intro h
      rcases h with ⟨hf, hg⟩
      change Continuous (fun x : X => (f x, g x))
      exact Continuous.prodMk hf hg
    · intro hpair
      have hf : Continuous (fun x : X => (pairing f g x).1) :=
        Continuous.fst hpair
      have hg : Continuous (fun x : X => (pairing f g x).2) :=
        Continuous.snd hpair
      have hf' : Continuous f := by
        simpa [pairing] using hf
      have hg' : Continuous g := by
        simpa [pairing] using hg
      exact And.intro hf' hg'

/-- Lemma 2.2: The functions `+`, `-`, `·`, `max`, and `min` on `ℝ × ℝ` are
continuous; the division function `(x,y) ↦ x / y` is continuous on
`ℝ × (ℝ \ {0})`; and for each `c : ℝ`, the function `m_c(x) = c * x` is
continuous. -/
lemma continuous_real_operations_and_scalar_mul :
    Continuous (fun p : ℝ × ℝ => p.1 + p.2) ∧
      Continuous (fun p : ℝ × ℝ => p.1 - p.2) ∧
        Continuous (fun p : ℝ × ℝ => p.1 * p.2) ∧
          Continuous (fun p : ℝ × ℝ => max p.1 p.2) ∧
            Continuous (fun p : ℝ × ℝ => min p.1 p.2) ∧
              Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => p.1 / p.2) ∧
                (∀ c : ℝ, Continuous (fun x : ℝ => c * x)) := by
  constructor
  · simpa using (continuous_fst.add continuous_snd)
  constructor
  · simpa using (continuous_fst.sub continuous_snd)
  constructor
  · simpa using (continuous_fst.mul continuous_snd)
  constructor
  · simpa using (continuous_max : Continuous (fun p : ℝ × ℝ => max p.1 p.2))
  constructor
  · simpa using (continuous_min : Continuous (fun p : ℝ × ℝ => min p.1 p.2))
  constructor
  ·
    have hfst :
        Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => p.1) := continuous_fst
    have hsnd :
        Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hdiv :
        Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => p.1 / (p.2 : ℝ)) :=
      Continuous.div hfst hsnd (fun p => p.2.property)
    simpa using hdiv
  ·
    intro c
    simpa using (continuous_const.mul continuous_id)

/-- Helper for Theorem 2.4: continuity of constant multiplication at a point. -/
lemma helperForTheorem_2_4_continuousAt_const_mul {X : Type*} [TopologicalSpace X]
    (c : ℝ) {f : X → ℝ} {x0 : X} (hf : ContinuousAt f x0) :
    ContinuousAt (fun x => c * f x) x0 := by
  have hc : ContinuousAt (fun _ : X => c) x0 := continuousAt_const
  simpa using hc.mul hf

/-- Helper for Theorem 2.4: continuity of constant multiplication. -/
lemma helperForTheorem_2_4_continuous_const_mul {X : Type*} [TopologicalSpace X]
    (c : ℝ) {f : X → ℝ} (hf : Continuous f) :
    Continuous (fun x => c * f x) := by
  simpa using (continuous_const.mul hf)

/-- Helper for Theorem 2.4: continuity of division under a global nonvanishing. -/
lemma helperForTheorem_2_4_continuousAt_div_of_forall_ne_zero {X : Type*}
    [TopologicalSpace X] {f g : X → ℝ} {x0 : X} (hf : ContinuousAt f x0)
    (hg : ContinuousAt g x0) (hgnz : ∀ x, g x ≠ 0) :
    ContinuousAt (fun x => f x / g x) x0 := by
  have h0 : g x0 ≠ 0 := hgnz x0
  simpa using hf.div hg h0

/-- Theorem 2.4: (a) If `f` and `g` are continuous at `x0`, then `f + g`,
`f - g`, `f g`, `max f g`, `min f g`, and `c f` are continuous at `x0`, and if
`g(x) ≠ 0` for all `x`, then `f/g` is continuous at `x0`. (b) If `f` and `g`
are continuous, then the same operations are continuous, and if `g(x) ≠ 0` for
all `x`, then `f/g` is continuous. -/
theorem continuous_operations_at_and_continuous {X : Type*} [MetricSpace X]
    (f g : X → ℝ) (c : ℝ) (x0 : X) :
    ((ContinuousAt f x0 ∧ ContinuousAt g x0) →
        (ContinuousAt (fun x => f x + g x) x0 ∧
          ContinuousAt (fun x => f x - g x) x0 ∧
            ContinuousAt (fun x => f x * g x) x0 ∧
              ContinuousAt (fun x => max (f x) (g x)) x0 ∧
                ContinuousAt (fun x => min (f x) (g x)) x0 ∧
                  ContinuousAt (fun x => c * f x) x0 ∧
                    ((∀ x : X, g x ≠ 0) →
                      ContinuousAt (fun x => f x / g x) x0))) ∧
      ((Continuous f ∧ Continuous g) →
        (Continuous (fun x => f x + g x) ∧
          Continuous (fun x => f x - g x) ∧
            Continuous (fun x => f x * g x) ∧
              Continuous (fun x => max (f x) (g x)) ∧
              Continuous (fun x => min (f x) (g x)) ∧
                Continuous (fun x => c * f x) ∧
                    ((∀ x : X, g x ≠ 0) →
                      Continuous (fun x => f x / g x)))) := by
  constructor
  · intro h
    rcases h with ⟨hf, hg⟩
    constructor
    · exact hf.add hg
    constructor
    · exact hf.sub hg
    constructor
    · exact hf.mul hg
    constructor
    · exact hf.max hg
    constructor
    · exact hf.min hg
    constructor
    · exact helperForTheorem_2_4_continuousAt_const_mul c hf
    · intro hgnz
      exact helperForTheorem_2_4_continuousAt_div_of_forall_ne_zero hf hg hgnz
  · intro h
    rcases h with ⟨hf, hg⟩
    constructor
    · exact hf.add hg
    constructor
    · exact hf.sub hg
    constructor
    · exact hf.mul hg
    constructor
    · exact hf.max hg
    constructor
    · exact hf.min hg
    constructor
    · exact helperForTheorem_2_4_continuous_const_mul c hf
    · intro hgnz
      exact hf.div hg hgnz

/-- Proposition 2.6: If `f : X → ℝ` is continuous on a metric space, then the
function `|f|` defined by `|f| (x) = |f x|` is continuous on `X`. -/
theorem continuous_abs_comp {X : Type*} [MetricSpace X] (f : X → ℝ)
    (hf : Continuous f) : Continuous (fun x => |f x|) := by
  simpa using hf.abs

/-- Proposition 2.7: The coordinate projections `π₁, π₂ : ℝ × ℝ → ℝ` are
continuous, and if `(X, d)` is a metric space with `f : ℝ → X` continuous,
then `g₁(x,y) = f x` and `g₂(x,y) = f y` are continuous. -/
theorem continuous_projections_and_coordinate_comp :
    (Continuous (fun p : ℝ × ℝ => p.1) ∧
        Continuous (fun p : ℝ × ℝ => p.2)) ∧
      (∀ {X : Type*} [MetricSpace X] {f : ℝ → X}, Continuous f →
        (Continuous (fun p : ℝ × ℝ => f p.1) ∧
          Continuous (fun p : ℝ × ℝ => f p.2))) := by
  constructor
  · constructor
    · simpa using (continuous_fst : Continuous (fun p : ℝ × ℝ => p.1))
    · simpa using (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
  · intro X _ f hf
    constructor
    ·
      simpa using
        (hf.comp (continuous_fst : Continuous (fun p : ℝ × ℝ => p.1)))
    ·
      simpa using
        (hf.comp (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2)))

/-- Helper for Proposition 2.8: continuity of a single monomial term. -/
lemma helperForProposition_2_8_continuous_monomial
    (c0 : ℝ) (i j : ℕ) :
    Continuous (fun p : ℝ × ℝ => c0 * (p.1 ^ i) * (p.2 ^ j)) := by
  have hfst : Continuous (fun p : ℝ × ℝ => p.1 ^ i) :=
    (continuous_pow i).comp (continuous_fst : Continuous (fun p : ℝ × ℝ => p.1))
  have hsnd : Continuous (fun p : ℝ × ℝ => p.2 ^ j) :=
    (continuous_pow j).comp (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
  exact (continuous_const.mul hfst).mul hsnd

/-- Helper for Proposition 2.8: continuity of the finite double sum defining `P`. -/
lemma helperForProposition_2_8_continuous_double_sum
    (n m : ℕ) (c : ℕ → ℕ → ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      Finset.sum (Finset.range (n + 1)) fun i =>
        Finset.sum (Finset.range (m + 1)) fun j =>
          c i j * (p.1 ^ i) * (p.2 ^ j)) := by
  refine continuous_finset_sum (Finset.range (n + 1)) ?_
  intro i hi
  refine continuous_finset_sum (Finset.range (m + 1)) ?_
  intro j hj
  exact helperForProposition_2_8_continuous_monomial (c i j) i j

/-- Helper for Proposition 2.8: continuity after composing with a pair of continuous maps. -/
lemma helperForProposition_2_8_continuous_comp
    {X : Type*} [MetricSpace X] {P : ℝ × ℝ → ℝ}
    (hP : Continuous P) {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => P (f x, g x)) := by
  have hpair : Continuous (fun x => (f x, g x)) := Continuous.prodMk hf hg
  exact hP.comp hpair

/-- Proposition 2.8: For integers `n, m ≥ 0` and coefficients `c_{ij} ∈ ℝ`,
define `P(x,y) = ∑_{i=0}^n ∑_{j=0}^m c_{ij} x^i y^j`. Then `P` is continuous
on `ℝ × ℝ`. Moreover, for any metric space `X` and continuous `f, g : X → ℝ`,
the map `x ↦ P (f x, g x)` is continuous. -/
theorem continuous_polynomial_two_variables
    (n m : ℕ) (c : ℕ → ℕ → ℝ) :
    let P : ℝ × ℝ → ℝ :=
        fun p =>
          Finset.sum (Finset.range (n + 1)) fun i =>
            Finset.sum (Finset.range (m + 1)) fun j =>
              c i j * (p.1 ^ i) * (p.2 ^ j)
    ;
    Continuous P ∧
      (∀ {X : Type*} [MetricSpace X] {f g : X → ℝ},
        Continuous f → Continuous g → Continuous (fun x => P (f x, g x))) := by
  simp
  constructor
  · exact helperForProposition_2_8_continuous_double_sum n m c
  · intro X _ f g hf hg
    let P : ℝ × ℝ → ℝ :=
      fun p =>
        Finset.sum (Finset.range (n + 1)) fun i =>
          Finset.sum (Finset.range (m + 1)) fun j =>
            c i j * (p.1 ^ i) * (p.2 ^ j)
    have hP : Continuous P :=
      helperForProposition_2_8_continuous_double_sum n m c
    have hcomp : Continuous (fun x => P (f x, g x)) :=
      helperForProposition_2_8_continuous_comp hP hf hg
    simpa [P] using hcomp

/-- Helper for Proposition 2.9: continuity of the pairing map into a product. -/
lemma helperForProposition_2_9_continuous_pairing {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g) :
    Continuous (pairing f g) := by
  change Continuous (fun x => (f x, g x))
  exact Continuous.prodMk hf hg

/-- Proposition 2.9: If `X` is a topological space and `f : X → ℝ^m`,
`g : X → ℝ^n` are continuous (with the Euclidean topologies), then the map
`x ↦ (f x, g x)` into `ℝ^m × ℝ^n ≃ ℝ^{m+n}` is continuous. -/
theorem continuous_pairing_euclidean {X : Type*} [TopologicalSpace X] {m n : ℕ}
    (f : X → EuclideanSpace ℝ (Fin m)) (g : X → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (pairing f g) := by
  exact helperForProposition_2_9_continuous_pairing f g hf hg

/-- Helper for Proposition 2.10: continuity of a monomial on `ℝ^k`. -/
lemma helperForProposition_2_10_continuous_monomial (k : ℕ) (multi : Fin k → ℕ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin k) =>
      Finset.prod Finset.univ (fun j => x j ^ (multi j))) := by
  refine continuous_finset_prod (s:=Finset.univ) ?_
  intro j hj
  have hcoord : Continuous (fun x : EuclideanSpace ℝ (Fin k) => x j) := by
    simpa using
      (PiLp.continuous_apply (p:=2) (β:=fun _ : Fin k => ℝ) j)
  exact hcoord.pow (multi j)

/-- Helper for Proposition 2.10: continuity of a weighted monomial term. -/
lemma helperForProposition_2_10_continuous_weighted_monomial (k : ℕ)
    (I : Finset (Fin k → ℕ)) (c : {i // i ∈ I} → ℝ) (i : {i // i ∈ I}) :
    Continuous (fun x : EuclideanSpace ℝ (Fin k) =>
      c i * Finset.prod Finset.univ (fun j => x j ^ (i.1 j))) := by
  have hprod :
      Continuous (fun x : EuclideanSpace ℝ (Fin k) =>
        Finset.prod Finset.univ (fun j => x j ^ (i.1 j))) :=
    helperForProposition_2_10_continuous_monomial k i.1
  exact continuous_const.mul hprod

/-- Proposition 2.10: Let `k ≥ 1`, let `I ⊆ ℕ^k` be finite, let `c : I → ℝ`,
and define `P : ℝ^k → ℝ` by
`P(x_1, ..., x_k) = ∑_{(i_1, ..., i_k) ∈ I} c(i_1, ..., i_k) * x_1^{i_1} * ... * x_k^{i_k}`.
Then `P` is continuous on `ℝ^k` (with the Euclidean topology). -/
theorem continuous_polynomial_multi_index (k : ℕ) (hk : 1 ≤ k)
    (I : Finset (Fin k → ℕ)) (c : {i // i ∈ I} → ℝ) :
    let P : EuclideanSpace ℝ (Fin k) → ℝ :=
        fun x =>
          Finset.sum I.attach (fun i =>
            c i * Finset.prod Finset.univ (fun j => x j ^ (i.1 j)))
    ;
    Continuous P := by
  simp
  refine continuous_finset_sum I.attach ?_
  intro i hi
  exact helperForProposition_2_10_continuous_weighted_monomial k I c i

/-- Sum distance on a product of metric spaces:
`d((x,y),(x',y')) = dist x x' + dist y y'`. -/
def prodSumDist (X Y : Type*) [MetricSpace X] [MetricSpace Y] :
    (X × Y) → (X × Y) → ℝ :=
  fun p q => dist p.1 q.1 + dist p.2 q.2

/-- Helper for Proposition 2.11: sum distance vanishes on identical points. -/
lemma helperForProposition_2_11_prodSumDist_self (X Y : Type*)
    [MetricSpace X] [MetricSpace Y] :
    ∀ p : X × Y, prodSumDist (X:=X) (Y:=Y) p p = 0 := by
  intro p
  simp [prodSumDist]

/-- Helper for Proposition 2.11: sum distance is symmetric. -/
lemma helperForProposition_2_11_prodSumDist_comm (X Y : Type*)
    [MetricSpace X] [MetricSpace Y] :
    ∀ p q : X × Y,
      prodSumDist (X:=X) (Y:=Y) p q = prodSumDist (X:=X) (Y:=Y) q p := by
  intro p q
  simp [prodSumDist, dist_comm]

/-- Helper for Proposition 2.11: sum distance satisfies the triangle inequality. -/
lemma helperForProposition_2_11_prodSumDist_triangle (X Y : Type*)
    [MetricSpace X] [MetricSpace Y] :
    ∀ p q r : X × Y,
      prodSumDist (X:=X) (Y:=Y) p r ≤
        prodSumDist (X:=X) (Y:=Y) p q + prodSumDist (X:=X) (Y:=Y) q r := by
  intro p q r
  have hx : dist p.1 r.1 ≤ dist p.1 q.1 + dist q.1 r.1 := dist_triangle _ _ _
  have hy : dist p.2 r.2 ≤ dist p.2 q.2 + dist q.2 r.2 := dist_triangle _ _ _
  have hsum :
      dist p.1 r.1 + dist p.2 r.2 ≤
        (dist p.1 q.1 + dist q.1 r.1) + (dist p.2 q.2 + dist q.2 r.2) :=
    add_le_add hx hy
  simpa [prodSumDist, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Proposition 2.11: zero sum distance implies equality. -/
lemma helperForProposition_2_11_eq_of_prodSumDist_eq_zero (X Y : Type*)
    [MetricSpace X] [MetricSpace Y] :
    ∀ {p q : X × Y},
      prodSumDist (X:=X) (Y:=Y) p q = 0 → p = q := by
  intro p q h
  have h' : dist p.1 q.1 + dist p.2 q.2 = 0 := by
    simpa [prodSumDist] using h
  have hx_nonneg : 0 ≤ dist p.1 q.1 := dist_nonneg
  have hy_nonneg : 0 ≤ dist p.2 q.2 := dist_nonneg
  have hx_le' : dist p.1 q.1 ≤ dist p.1 q.1 + dist p.2 q.2 := by
    exact le_add_of_nonneg_right hy_nonneg
  have hx_le : dist p.1 q.1 ≤ 0 := by
    simpa [h'] using hx_le'
  have hy_le' : dist p.2 q.2 ≤ dist p.1 q.1 + dist p.2 q.2 := by
    exact le_add_of_nonneg_left hx_nonneg
  have hy_le : dist p.2 q.2 ≤ 0 := by
    simpa [h'] using hy_le'
  have hx : dist p.1 q.1 = 0 := by
    exact le_antisymm hx_le hx_nonneg
  have hy : dist p.2 q.2 = 0 := by
    exact le_antisymm hy_le hy_nonneg
  have hx' : p.1 = q.1 := by
    exact eq_of_dist_eq_zero hx
  have hy' : p.2 = q.2 := by
    exact eq_of_dist_eq_zero hy
  exact Prod.ext hx' hy'

/-- Proposition 2.11: For metric spaces `(X, d_X)` and `(Y, d_Y)`, the function
`d_{X×Y}((x,y),(x',y')) = d_X(x,x') + d_Y(y,y')` is a metric on `X × Y`, hence
`(X × Y, d_{X×Y})` is a metric space. -/
theorem metricSpace_prod_sum_dist (X Y : Type*) [MetricSpace X] [MetricSpace Y] :
    ∃ m : MetricSpace (X × Y), m.dist = prodSumDist (X:=X) (Y:=Y) := by
  refine ⟨
    { dist := prodSumDist (X:=X) (Y:=Y),
      dist_self := helperForProposition_2_11_prodSumDist_self (X:=X) (Y:=Y),
      dist_comm := helperForProposition_2_11_prodSumDist_comm (X:=X) (Y:=Y),
      dist_triangle := helperForProposition_2_11_prodSumDist_triangle (X:=X) (Y:=Y),
      eq_of_dist_eq_zero :=
        helperForProposition_2_11_eq_of_prodSumDist_eq_zero (X:=X) (Y:=Y) },
    ?_⟩
  rfl

/-- Helper for Proposition 2.12: extract a two-variable ε-band from continuity. -/
lemma helperForProposition_2_12_eventually_Ioo_of_continuousAt
    (f : ℝ × ℝ → ℝ) (x0 y0 : ℝ) (hf : ContinuousAt f (x0, y0)) :
    ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ x in nhds x0, ∀ᶠ y in nhds y0,
        f (x, y) ∈ Set.Ioo (f (x0, y0) - ε) (f (x0, y0) + ε) := by
  intro ε hε
  set f0 : ℝ := f (x0, y0)
  have hdist : ∀ᶠ p in nhds (x0, y0), dist (f p) f0 < ε := by
    have h := (Metric.tendsto_nhds.1 hf.tendsto) ε hε
    simpa [f0] using h
  have hIoo :
      ∀ᶠ p in nhds (x0, y0), f p ∈ Set.Ioo (f0 - ε) (f0 + ε) := by
    refine hdist.mono ?_
    intro p hp
    have habs : |f p - f0| < ε := by
      simpa [Real.dist_eq] using hp
    have hlt : -ε < f p - f0 ∧ f p - f0 < ε := (abs_lt).1 habs
    have hleft : f0 - ε < f p := by
      linarith [hlt.1]
    have hright : f p < f0 + ε := by
      linarith [hlt.2]
    exact And.intro hleft hright
  have hprod :
      ∀ᶠ p in nhds x0 ×ˢ nhds y0, f p ∈ Set.Ioo (f0 - ε) (f0 + ε) := by
    simpa [nhds_prod_eq] using hIoo
  rcases (Filter.eventually_prod_iff).1 hprod with ⟨pa, hpa, pb, hpb, h⟩
  refine hpa.mono ?_
  intro x hx
  have hpb' : ∀ᶠ y in nhds y0, pb y := hpb
  exact hpb'.mono (fun y hy => h hx hy)

/-- Helper for Proposition 2.12: outer limsup (inner `y`) tends to `f (x0,y0)`. -/
lemma helperForProposition_2_12_tendsto_outer_limsup_inner_nhds
    (f : ℝ × ℝ → ℝ) (x0 y0 : ℝ) (hf : ContinuousAt f (x0, y0)) :
    Filter.Tendsto (fun x => Filter.limsup (fun y => f (x, y)) (nhds y0)) (nhds x0)
      (nhds (f (x0, y0))) := by
  set f0 : ℝ := f (x0, y0)
  refine (Metric.tendsto_nhds).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hIoo :
      ∀ᶠ x in nhds x0, ∀ᶠ y in nhds y0,
        f (x, y) ∈ Set.Ioo (f0 - ε / 2) (f0 + ε / 2) := by
    simpa [f0] using
      (helperForProposition_2_12_eventually_Ioo_of_continuousAt
        (f:=f) (x0:=x0) (y0:=y0) hf hε2)
  refine hIoo.mono ?_
  intro x hx
  have hupper_ev : ∀ᶠ y in nhds y0, f (x, y) ≤ f0 + ε / 2 := by
    refine hx.mono ?_
    intro y hy
    exact le_of_lt hy.2
  have hlower_ev : ∀ᶠ y in nhds y0, f0 - ε / 2 ≤ f (x, y) := by
    refine hx.mono ?_
    intro y hy
    exact le_of_lt hy.1
  have hco_le :
      Filter.IsCoboundedUnder (fun a b => a ≤ b) (nhds y0) (fun y => f (x, y)) :=
    Filter.isCoboundedUnder_le_of_eventually_le (l:=nhds y0)
      (f:=fun y => f (x, y)) (x:=f0 - ε / 2) hlower_ev
  have hco_ge :
      Filter.IsCoboundedUnder (fun a b => a ≥ b) (nhds y0) (fun y => f (x, y)) :=
    Filter.isCoboundedUnder_ge_of_eventually_le (l:=nhds y0)
      (f:=fun y => f (x, y)) (x:=f0 + ε / 2) hupper_ev
  have hupper :
      Filter.limsup (fun y => f (x, y)) (nhds y0) ≤ f0 + ε / 2 :=
    Filter.limsup_le_of_le (hf := hco_le) (h := hupper_ev)
  have hliminf :
      f0 - ε / 2 ≤ Filter.liminf (fun y => f (x, y)) (nhds y0) :=
    Filter.le_liminf_of_le (hf := hco_ge) (h := hlower_ev)
  have hbounded_le :
      Filter.IsBoundedUnder (fun a b => a ≤ b) (nhds y0) (fun y => f (x, y)) :=
    Filter.isBoundedUnder_of_eventually_le (f:=nhds y0)
      (u:=fun y => f (x, y)) (a:=f0 + ε / 2) hupper_ev
  have hbounded_ge :
      Filter.IsBoundedUnder (fun a b => a ≥ b) (nhds y0) (fun y => f (x, y)) :=
    Filter.isBoundedUnder_of_eventually_ge (f:=nhds y0)
      (u:=fun y => f (x, y)) (a:=f0 - ε / 2) hlower_ev
  have hlinf_le_lsup :
      Filter.liminf (fun y => f (x, y)) (nhds y0) ≤
        Filter.limsup (fun y => f (x, y)) (nhds y0) :=
    Filter.liminf_le_limsup (h:=hbounded_le) (h':=hbounded_ge)
  have hlow :
      f0 - ε / 2 ≤ Filter.limsup (fun y => f (x, y)) (nhds y0) :=
    le_trans hliminf hlinf_le_lsup
  have habs :
      |Filter.limsup (fun y => f (x, y)) (nhds y0) - f0| ≤ ε / 2 := by
    refine (abs_le).2 ?_
    constructor
    · linarith [hlow]
    · linarith [hupper]
  have hdist :
      dist (Filter.limsup (fun y => f (x, y)) (nhds y0)) f0 ≤ ε / 2 := by
    simpa [Real.dist_eq] using habs
  have hdelta : ε / 2 < ε := by linarith
  exact lt_of_le_of_lt hdist hdelta

/-- Helper for Proposition 2.12: outer liminf (inner `y`) tends to `f (x0,y0)`. -/
lemma helperForProposition_2_12_tendsto_outer_liminf_inner_nhds
    (f : ℝ × ℝ → ℝ) (x0 y0 : ℝ) (hf : ContinuousAt f (x0, y0)) :
    Filter.Tendsto (fun x => Filter.liminf (fun y => f (x, y)) (nhds y0)) (nhds x0)
      (nhds (f (x0, y0))) := by
  set f0 : ℝ := f (x0, y0)
  refine (Metric.tendsto_nhds).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hIoo :
      ∀ᶠ x in nhds x0, ∀ᶠ y in nhds y0,
        f (x, y) ∈ Set.Ioo (f0 - ε / 2) (f0 + ε / 2) := by
    simpa [f0] using
      (helperForProposition_2_12_eventually_Ioo_of_continuousAt
        (f:=f) (x0:=x0) (y0:=y0) hf hε2)
  refine hIoo.mono ?_
  intro x hx
  have hupper_ev : ∀ᶠ y in nhds y0, f (x, y) ≤ f0 + ε / 2 := by
    refine hx.mono ?_
    intro y hy
    exact le_of_lt hy.2
  have hlower_ev : ∀ᶠ y in nhds y0, f0 - ε / 2 ≤ f (x, y) := by
    refine hx.mono ?_
    intro y hy
    exact le_of_lt hy.1
  have hco_le :
      Filter.IsCoboundedUnder (fun a b => a ≤ b) (nhds y0) (fun y => f (x, y)) :=
    Filter.isCoboundedUnder_le_of_eventually_le (l:=nhds y0)
      (f:=fun y => f (x, y)) (x:=f0 - ε / 2) hlower_ev
  have hco_ge :
      Filter.IsCoboundedUnder (fun a b => a ≥ b) (nhds y0) (fun y => f (x, y)) :=
    Filter.isCoboundedUnder_ge_of_eventually_le (l:=nhds y0)
      (f:=fun y => f (x, y)) (x:=f0 + ε / 2) hupper_ev
  have hupper :
      Filter.limsup (fun y => f (x, y)) (nhds y0) ≤ f0 + ε / 2 :=
    Filter.limsup_le_of_le (hf := hco_le) (h := hupper_ev)
  have hliminf_low :
      f0 - ε / 2 ≤ Filter.liminf (fun y => f (x, y)) (nhds y0) :=
    Filter.le_liminf_of_le (hf := hco_ge) (h := hlower_ev)
  have hbounded_le :
      Filter.IsBoundedUnder (fun a b => a ≤ b) (nhds y0) (fun y => f (x, y)) :=
    Filter.isBoundedUnder_of_eventually_le (f:=nhds y0)
      (u:=fun y => f (x, y)) (a:=f0 + ε / 2) hupper_ev
  have hbounded_ge :
      Filter.IsBoundedUnder (fun a b => a ≥ b) (nhds y0) (fun y => f (x, y)) :=
    Filter.isBoundedUnder_of_eventually_ge (f:=nhds y0)
      (u:=fun y => f (x, y)) (a:=f0 - ε / 2) hlower_ev
  have hlinf_le_lsup :
      Filter.liminf (fun y => f (x, y)) (nhds y0) ≤
        Filter.limsup (fun y => f (x, y)) (nhds y0) :=
    Filter.liminf_le_limsup (h:=hbounded_le) (h':=hbounded_ge)
  have hupper_liminf :
      Filter.liminf (fun y => f (x, y)) (nhds y0) ≤ f0 + ε / 2 :=
    le_trans hlinf_le_lsup hupper
  have habs :
      |Filter.liminf (fun y => f (x, y)) (nhds y0) - f0| ≤ ε / 2 := by
    refine (abs_le).2 ?_
    constructor
    · linarith [hliminf_low]
    · linarith [hupper_liminf]
  have hdist :
      dist (Filter.liminf (fun y => f (x, y)) (nhds y0)) f0 ≤ ε / 2 := by
    simpa [Real.dist_eq] using habs
  have hdelta : ε / 2 < ε := by linarith
  exact lt_of_le_of_lt hdist hdelta

/-- Helper for Proposition 2.12: a `nhds`-limit forces the point value in a `T1` space. -/
lemma helperForProposition_2_12_tendsto_nhds_forces_value_at_point
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    {x0 : X} {g : X → Y} {a : Y} (h : Filter.Tendsto g (nhds x0) (nhds a)) :
    g x0 = a := by
  have hle : pure x0 ≤ nhds x0 :=
    (pure_le_nhds : (pure : X → Filter X) ≤ nhds) x0
  have hmap : Filter.map g (pure x0) ≤ Filter.map g (nhds x0) :=
    (Filter.map_mono (m:=g)) hle
  have hmap' : Filter.map g (pure x0) ≤ nhds a := le_trans hmap h
  have hpure : pure (g x0) ≤ nhds a := by
    have hmap_eq : Filter.map g (pure x0) = pure (g x0) := by
      simpa using (Filter.map_pure g x0)
    simpa [hmap_eq] using hmap'
  exact (pure_le_nhds_iff).1 hpure

/-- Helper for Proposition 2.12: identify section limits at the point. -/
lemma helperForProposition_2_12_limUnder_section_at_point_eq
    (f : ℝ × ℝ → ℝ) (x0 y0 : ℝ) (hf : ContinuousAt f (x0, y0)) :
    limUnder (nhds y0) (fun y => f (x0, y)) = f (x0, y0) ∧
      limUnder (nhds x0) (fun x => f (x, y0)) = f (x0, y0) := by
  constructor
  ·
    have hpair : ContinuousAt (fun y : ℝ => (x0, y)) y0 :=
      ContinuousAt.prodMk continuousAt_const continuousAt_id
    have hy : ContinuousAt (fun y : ℝ => f (x0, y)) y0 := by
      simpa [Function.comp] using
        (ContinuousAt.comp (g:=f) (f:=fun y : ℝ => (x0, y)) hf hpair)
    have hlim :
        limUnder (nhds y0) (fun y => f (x0, y)) = f (x0, y0) :=
      Filter.Tendsto.limUnder_eq hy.tendsto
    exact hlim
  ·
    have hpair : ContinuousAt (fun x : ℝ => (x, y0)) x0 :=
      ContinuousAt.prodMk continuousAt_id continuousAt_const
    have hx : ContinuousAt (fun x : ℝ => f (x, y0)) x0 := by
      simpa [Function.comp] using
        (ContinuousAt.comp (g:=f) (f:=fun x : ℝ => (x, y0)) hf hpair)
    have hlim :
        limUnder (nhds x0) (fun x => f (x, y0)) = f (x0, y0) :=
      Filter.Tendsto.limUnder_eq hx.tendsto
    exact hlim

/-- Proposition 2.12: If `f : ℝ × ℝ → ℝ` is continuous at `(x0, y0)`, then
`lim_{x→x0} limsup_{y→y0} f(x, y) = lim_{y→y0} limsup_{x→x0} f(x, y) = f(x0, y0)`
and
`lim_{x→x0} liminf_{y→y0} f(x, y) = lim_{y→y0} liminf_{x→x0} f(x, y) = f(x0, y0)`.
In particular, if both iterated limits exist, then
`lim_{x→x0} lim_{y→y0} f(x, y) = lim_{y→y0} lim_{x→x0} f(x, y)`. -/
theorem iterated_limsup_liminf_eq_of_continuousAt
    (f : ℝ × ℝ → ℝ) (x0 y0 : ℝ) (hf : ContinuousAt f (x0, y0)) :
    (Filter.Tendsto (fun x => Filter.limsup (fun y => f (x, y)) (nhds y0)) (nhds x0)
        (nhds (f (x0, y0))) ∧
      Filter.Tendsto (fun y => Filter.limsup (fun x => f (x, y)) (nhds x0)) (nhds y0)
        (nhds (f (x0, y0)))) ∧
    (Filter.Tendsto (fun x => Filter.liminf (fun y => f (x, y)) (nhds y0)) (nhds x0)
        (nhds (f (x0, y0))) ∧
      Filter.Tendsto (fun y => Filter.liminf (fun x => f (x, y)) (nhds x0)) (nhds y0)
        (nhds (f (x0, y0)))) ∧
    (∀ {L1 L2 : ℝ},
        Filter.Tendsto (fun x => limUnder (nhds y0) (fun y => f (x, y))) (nhds x0) (nhds L1) →
        Filter.Tendsto (fun y => limUnder (nhds x0) (fun x => f (x, y))) (nhds y0) (nhds L2) →
        L1 = L2) := by
  have hlimsup_x :
      Filter.Tendsto (fun x => Filter.limsup (fun y => f (x, y)) (nhds y0)) (nhds x0)
        (nhds (f (x0, y0))) :=
    helperForProposition_2_12_tendsto_outer_limsup_inner_nhds (f:=f) (x0:=x0) (y0:=y0) hf
  let g : ℝ × ℝ → ℝ := fun p => f (p.2, p.1)
  have hswap : ContinuousAt (fun p : ℝ × ℝ => (p.2, p.1)) (y0, x0) :=
    continuous_swap.continuousAt
  have hg : ContinuousAt g (y0, x0) := by
    simpa [g, Function.comp] using
      (ContinuousAt.comp (g:=f) (f:=fun p : ℝ × ℝ => (p.2, p.1)) hf hswap)
  have hlimsup_y :
      Filter.Tendsto (fun y => Filter.limsup (fun x => f (x, y)) (nhds x0)) (nhds y0)
        (nhds (f (x0, y0))) := by
    have h :=
      helperForProposition_2_12_tendsto_outer_limsup_inner_nhds (f:=g) (x0:=y0) (y0:=x0) hg
    simpa [g] using h
  have hliminf_x :
      Filter.Tendsto (fun x => Filter.liminf (fun y => f (x, y)) (nhds y0)) (nhds x0)
        (nhds (f (x0, y0))) :=
    helperForProposition_2_12_tendsto_outer_liminf_inner_nhds (f:=f) (x0:=x0) (y0:=y0) hf
  have hliminf_y :
      Filter.Tendsto (fun y => Filter.liminf (fun x => f (x, y)) (nhds x0)) (nhds y0)
        (nhds (f (x0, y0))) := by
    have h :=
      helperForProposition_2_12_tendsto_outer_liminf_inner_nhds (f:=g) (x0:=y0) (y0:=x0) hg
    simpa [g] using h
  refine And.intro ?_ ?_
  · exact And.intro hlimsup_x hlimsup_y
  · refine And.intro ?_ ?_
    · exact And.intro hliminf_x hliminf_y
    · intro L1 L2 hL1 hL2
      have hsections :
          limUnder (nhds y0) (fun y => f (x0, y)) = f (x0, y0) ∧
            limUnder (nhds x0) (fun x => f (x, y0)) = f (x0, y0) :=
        helperForProposition_2_12_limUnder_section_at_point_eq (f:=f) (x0:=x0) (y0:=y0) hf
      have hL1_at :
          (fun x => limUnder (nhds y0) (fun y => f (x, y))) x0 = L1 :=
        helperForProposition_2_12_tendsto_nhds_forces_value_at_point
          (x0:=x0)
          (g:=fun x => limUnder (nhds y0) (fun y => f (x, y))) (a:=L1) hL1
      have hL2_at :
          (fun y => limUnder (nhds x0) (fun x => f (x, y))) y0 = L2 :=
        helperForProposition_2_12_tendsto_nhds_forces_value_at_point
          (x0:=y0)
          (g:=fun y => limUnder (nhds x0) (fun x => f (x, y))) (a:=L2) hL2
      have hL1_eq : L1 = f (x0, y0) := by
        have h1 : L1 = limUnder (nhds y0) (fun y => f (x0, y)) := by
          simpa using hL1_at.symm
        exact h1.trans hsections.1
      have hL2_eq : L2 = f (x0, y0) := by
        have h2 : L2 = limUnder (nhds x0) (fun x => f (x, y0)) := by
          simpa using hL2_at.symm
        exact h2.trans hsections.2
      exact hL1_eq.trans hL2_eq.symm

/-- Proposition 2.13: A jointly continuous function `f : ℝ × ℝ → ℝ` is
continuous in each variable separately; for each `x`, the map `y ↦ f (x, y)`
is continuous, and for each `y`, the map `x ↦ f (x, y)` is continuous. -/
theorem continuous_in_each_variable_of_continuous (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) :
    (∀ x : ℝ, Continuous (fun y : ℝ => f (x, y))) ∧
      (∀ y : ℝ, Continuous (fun x : ℝ => f (x, y))) := by
  constructor
  · intro x
    simpa using hf.comp (Continuous.prodMk_right x)
  · intro y
    simpa using hf.comp (Continuous.prodMk_left y)

/-- The function `f(x,y) = xy / (x^2 + y^2)` for `(x,y) ≠ (0,0)`, and `0` at `(0,0)`. -/
noncomputable def separateContinuityExample : ℝ × ℝ → ℝ :=
  fun p =>
    if p = (0, 0) then 0 else (p.1 * p.2) / (p.1 ^ 2 + p.2 ^ 2)

/-- Helper for Proposition 2.14: nonvanishing of `x^2 + y^2` when `x ≠ 0`. -/
lemma helperForProposition_2_14_denominator_ne_zero_of_left_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ∀ y : ℝ, x ^ 2 + y ^ 2 ≠ 0 := by
  intro y
  have hxpos : 0 < x ^ 2 := by
    exact sq_pos_of_ne_zero hx
  have hypos : 0 ≤ y ^ 2 := by
    exact sq_nonneg y
  have hsum : 0 < x ^ 2 + y ^ 2 := by
    exact add_pos_of_pos_of_nonneg hxpos hypos
  exact ne_of_gt hsum

/-- Helper for Proposition 2.14: nonvanishing of `x^2 + y^2` when `y ≠ 0`. -/
lemma helperForProposition_2_14_denominator_ne_zero_of_right_ne_zero {y : ℝ} (hy : y ≠ 0) :
    ∀ x : ℝ, x ^ 2 + y ^ 2 ≠ 0 := by
  intro x
  have hypos : 0 < y ^ 2 := by
    exact sq_pos_of_ne_zero hy
  have hxpos : 0 ≤ x ^ 2 := by
    exact sq_nonneg x
  have hsum : 0 < x ^ 2 + y ^ 2 := by
    exact add_pos_of_nonneg_of_pos hxpos hypos
  exact ne_of_gt hsum

/-- Helper for Proposition 2.14: continuity of the rational expression with fixed nonzero `x`. -/
lemma helperForProposition_2_14_continuous_rational_fix_left {x : ℝ} (hx : x ≠ 0) :
    Continuous (fun y : ℝ => (x * y) / (x ^ 2 + y ^ 2)) := by
  have hnum : Continuous (fun y : ℝ => x * y) := by
    simpa using (continuous_const.mul continuous_id)
  have hpow : Continuous (fun y : ℝ => y ^ 2) := by
    simpa using (continuous_pow 2)
  have hden : Continuous (fun y : ℝ => x ^ 2 + y ^ 2) := by
    simpa using (continuous_const.add hpow)
  have hdenom : ∀ y : ℝ, x ^ 2 + y ^ 2 ≠ 0 :=
    helperForProposition_2_14_denominator_ne_zero_of_left_ne_zero (x:=x) hx
  exact Continuous.div hnum hden hdenom

/-- Helper for Proposition 2.14: continuity of the rational expression with fixed nonzero `y`. -/
lemma helperForProposition_2_14_continuous_rational_fix_right {y : ℝ} (hy : y ≠ 0) :
    Continuous (fun x : ℝ => (x * y) / (x ^ 2 + y ^ 2)) := by
  have hnum : Continuous (fun x : ℝ => x * y) := by
    simpa using (continuous_id.mul continuous_const)
  have hpow : Continuous (fun x : ℝ => x ^ 2) := by
    simpa using (continuous_pow 2)
  have hden : Continuous (fun x : ℝ => x ^ 2 + y ^ 2) := by
    simpa using (hpow.add continuous_const)
  have hdenom : ∀ x : ℝ, x ^ 2 + y ^ 2 ≠ 0 :=
    helperForProposition_2_14_denominator_ne_zero_of_right_ne_zero (y:=y) hy
  exact Continuous.div hnum hden hdenom

/-- Helper for Proposition 2.14: simplify the `y`-section when `x ≠ 0`. -/
lemma helperForProposition_2_14_simp_section_of_left_ne_zero {x : ℝ} (hx : x ≠ 0) :
    (fun y : ℝ => separateContinuityExample (x, y)) =
      (fun y : ℝ => (x * y) / (x ^ 2 + y ^ 2)) := by
  funext y
  have hxy : (x, y) ≠ (0, 0) := by
    intro hxy
    have hx0 : x = 0 := by
      have h := congrArg Prod.fst hxy
      simpa using h
    exact hx hx0
  simp [separateContinuityExample, hxy]

/-- Helper for Proposition 2.14: simplify the `x`-section when `y ≠ 0`. -/
lemma helperForProposition_2_14_simp_section_of_right_ne_zero {y : ℝ} (hy : y ≠ 0) :
    (fun x : ℝ => separateContinuityExample (x, y)) =
      (fun x : ℝ => (x * y) / (x ^ 2 + y ^ 2)) := by
  funext x
  have hxy : (x, y) ≠ (0, 0) := by
    intro hxy
    have hy0 : y = 0 := by
      have h := congrArg Prod.snd hxy
      simpa using h
    exact hy hy0
  simp [separateContinuityExample, hxy]

/-- Helper for Proposition 2.14: the `y`-section at `x = 0` is identically zero. -/
lemma helperForProposition_2_14_section_left_zero :
    (fun y : ℝ => separateContinuityExample (0, y)) = (fun _ => (0 : ℝ)) := by
  funext y
  by_cases hy : y = 0
  · subst hy
    simp [separateContinuityExample]
  · have hxy : (0, y) ≠ (0, 0) := by
      intro hxy
      apply hy
      have h := congrArg Prod.snd hxy
      simpa using h
    simp [separateContinuityExample]

/-- Helper for Proposition 2.14: the `x`-section at `y = 0` is identically zero. -/
lemma helperForProposition_2_14_section_right_zero :
    (fun x : ℝ => separateContinuityExample (x, 0)) = (fun _ => (0 : ℝ)) := by
  funext x
  by_cases hx : x = 0
  · subst hx
    simp [separateContinuityExample]
  · have hxy : (x, 0) ≠ (0, 0) := by
      intro hxy
      apply hx
      have h := congrArg Prod.fst hxy
      simpa using h
    simp [separateContinuityExample]

/-- Proposition 2.14: For the function `f : ℝ × ℝ → ℝ` defined by
`f(x,y) = xy / (x^2 + y^2)` for `(x,y) ≠ (0,0)` and `f(0,0) = 0`,
(i) for each fixed `x`, the map `y ↦ f(x,y)` is continuous on `ℝ`;
(ii) for each fixed `y`, the map `x ↦ f(x,y)` is continuous on `ℝ`. -/
theorem continuous_in_each_variable_separateContinuityExample :
    (∀ x : ℝ, Continuous (fun y : ℝ => separateContinuityExample (x, y))) ∧
      (∀ y : ℝ, Continuous (fun x : ℝ => separateContinuityExample (x, y))) := by
  constructor
  · intro x
    by_cases hx : x = 0
    · subst hx
      have hsection :
          (fun y : ℝ => separateContinuityExample (0, y)) = (fun _ => (0 : ℝ)) :=
        helperForProposition_2_14_section_left_zero
      simpa [hsection] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    · have hsection :
          (fun y : ℝ => separateContinuityExample (x, y)) =
            (fun y : ℝ => (x * y) / (x ^ 2 + y ^ 2)) :=
        helperForProposition_2_14_simp_section_of_left_ne_zero (x:=x) hx
      have hcont : Continuous (fun y : ℝ => (x * y) / (x ^ 2 + y ^ 2)) :=
        helperForProposition_2_14_continuous_rational_fix_left (x:=x) hx
      simpa [hsection] using hcont
  · intro y
    by_cases hy : y = 0
    · subst hy
      have hsection :
          (fun x : ℝ => separateContinuityExample (x, 0)) = (fun _ => (0 : ℝ)) :=
        helperForProposition_2_14_section_right_zero
      simpa [hsection] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    · have hsection :
          (fun x : ℝ => separateContinuityExample (x, y)) =
            (fun x : ℝ => (x * y) / (x ^ 2 + y ^ 2)) :=
        helperForProposition_2_14_simp_section_of_right_ne_zero (y:=y) hy
      have hcont : Continuous (fun x : ℝ => (x * y) / (x ^ 2 + y ^ 2)) :=
        helperForProposition_2_14_continuous_rational_fix_right (y:=y) hy
      simpa [hsection] using hcont

end Section02
end Chap02
