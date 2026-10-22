/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap07
section Section03

section

universe u

variable (X : Type u) [PseudoMetricSpace X]

/-- Definition 7.3.1. A sequence in a metric space `(X, d)` is a function
`x : ℕ → X`, written `xₙ` for its terms and `{xₙ}` for the whole sequence. It is
bounded if there exists `p ∈ X` and `B ∈ ℝ` such that `dist p (xₙ) ≤ B` for all
`n`. Equivalently, the image set `{xₙ : n ∈ ℕ}` is bounded. A subsequence of
`{xₙ}` is any sequence of the form `{x_{n_k}}` where `n_{k+1} > n_k` for all
`k`. -/
def MetricSequence (X : Type u) : Type u :=
  ℕ → X

variable {X}

/-- A sequence is bounded when all of its terms lie in a ball of finite radius
around some point of the space. -/
def MetricBoundedSequence (x : MetricSequence X) : Prop :=
  ∃ p : X, ∃ B : ℝ, ∀ n, dist p (x n) ≤ B

/-- A bounded sequence's range lies in a closed ball. -/
lemma range_subset_closedBall_of_boundedSequence (x : MetricSequence X) :
    MetricBoundedSequence (X := X) x →
      ∃ p B, Set.range x ⊆ Metric.closedBall p B := by
  rintro ⟨p, B, hB⟩
  refine ⟨p, B, ?_⟩
  intro y hy
  rcases hy with ⟨n, rfl⟩
  exact (Metric.mem_closedBall).2 (by simpa [dist_comm] using hB n)

/-- A bounded range yields a pointwise distance bound for the sequence. -/
lemma metricBoundedSequence_of_isBounded_range (x : MetricSequence X) :
    Bornology.IsBounded (Set.range x) → MetricBoundedSequence (X := X) x := by
  intro h
  obtain ⟨B, hB⟩ := h.subset_closedBall (x 0)
  refine ⟨x 0, B, ?_⟩
  intro n
  have hx : x n ∈ Set.range x := ⟨n, rfl⟩
  have hx' : x n ∈ Metric.closedBall (x 0) B := hB hx
  exact (Metric.mem_closedBall').1 hx'

/-- The book's notion of a bounded sequence agrees with boundedness of its
range in the bornology of the metric space. -/
theorem metricBoundedSequence_iff_isBounded_range (x : MetricSequence X) :
    MetricBoundedSequence (X := X) x ↔ Bornology.IsBounded (Set.range x) := by
  constructor
  · intro hx
    obtain ⟨p, B, hsub⟩ := range_subset_closedBall_of_boundedSequence (X := X) x hx
    exact (Metric.isBounded_closedBall (x := p) (r := B)).subset hsub
  · intro hx
    exact metricBoundedSequence_of_isBounded_range (X := X) x hx

/-- A subsequence of `x` is obtained by precomposing with a strictly increasing
map of indices. -/
def IsMetricSubsequence (y x : MetricSequence X) : Prop :=
  ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, y k = x (n k)

/-- Definition 7.3.2. A sequence `{xₙ}` in a metric space converges to a point
`p` if for every `ε > 0` there exists `M ∈ ℕ` such that `dist (xₙ) p < ε` for
all `n ≥ M`. In this case `p` is a limit of the sequence. -/
def MetricConvergesTo (x : MetricSequence X) (p : X) : Prop :=
  ∀ ε > 0, ∃ M : ℕ, ∀ ⦃n⦄, M ≤ n → dist (x n) p < ε

/-- A sequence is convergent when it has a (not necessarily unique) limit. -/
def MetricConvergentSequence (x : MetricSequence X) : Prop :=
  ∃ p : X, MetricConvergesTo (X := X) x p

/-- The book's notion of convergence agrees with the usual filter convergence
of sequences. -/
theorem metricConvergesTo_iff_tendsto (x : MetricSequence X) (p : X) :
    MetricConvergesTo (X := X) x p ↔ Filter.Tendsto x Filter.atTop (nhds p) := by
  simpa [MetricConvergesTo] using (Metric.tendsto_atTop (u := x) (a := p)).symm

/-- A sequence is divergent when it does not converge. -/
def MetricDivergentSequence (x : MetricSequence X) : Prop :=
  ¬ MetricConvergentSequence (X := X) x

/-- Proposition 7.3.3. A convergent sequence in a metric space has a unique
limit. -/
theorem metricConvergentSequence_limit_unique {X : Type u} [MetricSpace X]
    {x : MetricSequence X} {p q : X} (hp : MetricConvergesTo (X := X) x p)
    (hq : MetricConvergesTo (X := X) x q) : p = q := by
  classical
  have hε : ∀ ε > 0, dist p q < ε := by
    intro ε hεpos
    obtain ⟨M1, hM1⟩ := hp (ε / 2) (by have h := half_pos hεpos; linarith)
    obtain ⟨M2, hM2⟩ := hq (ε / 2) (by have h := half_pos hεpos; linarith)
    let n := Nat.max M1 M2
    have hx1 : dist p (x n) < ε / 2 := by
      have hx := hM1 (n := n) (Nat.le_max_left _ _)
      simpa [n, dist_comm] using hx
    have hx2 : dist (x n) q < ε / 2 := by
      have hx := hM2 (n := n) (Nat.le_max_right _ _)
      simpa [n] using hx
    have htriangle :
        dist p q ≤ dist p (x n) + dist (x n) q := by
      have := dist_triangle (x := p) (y := x n) (z := q)
      simpa [n] using this
    have hsum : dist p (x n) + dist (x n) q < ε := by
      have hlt : dist p (x n) + dist (x n) q < ε / 2 + ε / 2 :=
        add_lt_add hx1 hx2
      have hadd : ε / 2 + ε / 2 = ε := by ring
      simpa [hadd] using hlt
    exact lt_of_le_of_lt htriangle hsum
  have hzero : dist p q = 0 := by
    by_contra hne
    have hpos : 0 < dist p q := lt_of_le_of_ne (dist_nonneg) (by simpa [eq_comm] using hne)
    have hlt := hε (dist p q / 2) (by have h := half_pos hpos; linarith)
    linarith
  exact dist_eq_zero.mp hzero

/-- Proposition 7.3.4. A convergent sequence in a metric space is bounded. -/
theorem metricConvergentSequence_bounded {X : Type u} [PseudoMetricSpace X]
    {x : MetricSequence X} (hx : MetricConvergentSequence (X := X) x) :
    MetricBoundedSequence (X := X) x := by
  classical
  rcases hx with ⟨p, hp⟩
  obtain ⟨M, hM⟩ := hp 1 (by exact one_pos)
  let s : Finset ℝ := (Finset.range (M + 1)).image (fun n => dist p (x n))
  have hs : s.Nonempty := by
    refine ⟨dist p (x 0), ?_⟩
    refine (Finset.mem_image).2 ?_
    refine ⟨0, ?_, rfl⟩
    exact (Finset.mem_range).2 (Nat.succ_pos M)
  -- Helper: distances in the initial segment are bounded by the finite max.
  have hinit : ∀ {n}, n < M → dist p (x n) ≤ s.max' hs := by
    intro n hn
    have hmem : dist p (x n) ∈ s := by
      refine (Finset.mem_image).2 ?_
      refine ⟨n, ?_, rfl⟩
      exact (Finset.mem_range).2 (Nat.lt_succ_of_lt hn)
    have hle' :
        dist p (x n) ≤ s.max' ⟨dist p (x n), hmem⟩ :=
      Finset.le_max' (s := s) (x := dist p (x n)) hmem
    have hproof : (⟨dist p (x n), hmem⟩ : s.Nonempty) = hs := by
      apply Subsingleton.elim
    simpa [hproof] using hle'
  -- Helper: the tail is bounded by 1 via convergence.
  have htail : ∀ {n}, M ≤ n → dist p (x n) ≤ 1 := by
    intro n hn
    have hlt : dist (x n) p < 1 := hM hn
    have hle : dist (x n) p ≤ 1 := le_of_lt hlt
    simpa [dist_comm] using hle
  refine ⟨p, max 1 (s.max' hs), ?_⟩
  intro n
  by_cases hn : n < M
  · have hle : dist p (x n) ≤ s.max' hs := hinit hn
    exact le_trans hle (le_max_right _ _)
  · have hle : dist p (x n) ≤ 1 := htail (le_of_not_gt hn)
    exact le_trans hle (le_max_left _ _)

/-- Nonnegative reals have distance to zero equal to themselves. -/
lemma real_dist_eq_self_of_nonneg {r : ℝ} (hr : 0 ≤ r) : dist r 0 = r := by
  simp [abs_of_nonneg hr]

/-- Distances to a limit point converge to zero. -/
lemma metricConvergesTo_dist_to_zero {X : Type u} [PseudoMetricSpace X]
    {x : MetricSequence X} {p : X} (hx : MetricConvergesTo (X := X) x p) :
    MetricConvergesTo (X := ℝ) (fun n => dist (x n) p) 0 := by
  intro ε hεpos
  obtain ⟨M, hM⟩ := hx ε hεpos
  refine ⟨M, ?_⟩
  intro n hn
  have hlt : dist (x n) p < ε := hM hn
  have hnonneg : 0 ≤ dist (x n) p := by
    exact dist_nonneg
  simpa [real_dist_eq_self_of_nonneg hnonneg] using hlt

/-- A distance bound by a sequence tending to zero forces convergence. -/
lemma metricConvergesTo_of_dist_le_of_tendsto {X : Type u} [PseudoMetricSpace X]
    {x : MetricSequence X} {p : X} {a : ℕ → ℝ} (ha : ∀ n, dist (x n) p ≤ a n)
    (hat : Filter.Tendsto a Filter.atTop (nhds (0 : ℝ))) :
    MetricConvergesTo (X := X) x p := by
  have ha0 : MetricConvergesTo (X := ℝ) a 0 :=
    (metricConvergesTo_iff_tendsto (X := ℝ) a 0).2 hat
  intro ε hεpos
  obtain ⟨M, hM⟩ := ha0 ε hεpos
  refine ⟨M, ?_⟩
  intro n hn
  have hle : dist (x n) p ≤ a n := ha n
  have hnonneg : 0 ≤ a n := by
    have hnonneg' : 0 ≤ dist (x n) p := by
      exact dist_nonneg
    exact le_trans hnonneg' hle
  have hlt : dist (a n) 0 < ε := hM hn
  have hlt' : a n < ε := by
    simpa [real_dist_eq_self_of_nonneg hnonneg] using hlt
  exact lt_of_le_of_lt hle hlt'

/-- Proposition 7.3.5. A sequence in a metric space converges to `p` if and
only if there is a real sequence controlling the distances to `p` that itself
tends to zero. -/
theorem metricConvergesTo_iff_exists_distance_bound {X : Type u} [PseudoMetricSpace X]
    {x : MetricSequence X} {p : X} :
    MetricConvergesTo (X := X) x p ↔
      ∃ a : ℕ → ℝ, (∀ n, dist (x n) p ≤ a n) ∧
        Filter.Tendsto a Filter.atTop (nhds (0 : ℝ)) := by
  constructor
  · intro hx
    refine ⟨fun n => dist (x n) p, ?_, ?_⟩
    · intro n
      exact le_rfl
    · have hx' :
        MetricConvergesTo (X := ℝ) (fun n => dist (x n) p) 0 :=
        metricConvergesTo_dist_to_zero (X := X) (x := x) (p := p) hx
      exact (metricConvergesTo_iff_tendsto (X := ℝ) (fun n => dist (x n) p) 0).1 hx'
  · rintro ⟨a, ha, hat⟩
    exact metricConvergesTo_of_dist_le_of_tendsto (X := X) (x := x) (p := p) ha hat

/-- Proposition 7.3.6. (i) A subsequence of a sequence converging to `p`
also converges to `p`. (ii) If some tail of a sequence converges to `p`, then
the original sequence converges to `p`. -/
theorem metricConvergesTo_subsequence {X : Type u} [PseudoMetricSpace X]
    {x y : MetricSequence X} {p : X} (hx : MetricConvergesTo (X := X) x p)
    (hy : IsMetricSubsequence (X := X) y x) :
    MetricConvergesTo (X := X) y p := by
  rcases hy with ⟨n, hnmono, hyx⟩
  intro ε hεpos
  obtain ⟨M, hM⟩ := hx ε hεpos
  refine ⟨M, ?_⟩
  intro k hk
  have hkn : M ≤ n k := le_trans hk (StrictMono.le_apply hnmono)
  have hdist : dist (x (n k)) p < ε := hM hkn
  simpa [hyx k] using hdist

theorem metricConvergesTo_of_tail {X : Type u} [PseudoMetricSpace X]
    {x : MetricSequence X} {p : X} {K : ℕ}
    (hx : MetricConvergesTo (X := X) (fun n => x (n + K.succ)) p) :
    MetricConvergesTo (X := X) x p := by
  intro ε hεpos
  obtain ⟨M, hM⟩ := hx ε hεpos
  refine ⟨M + K.succ, ?_⟩
  intro n hn
  have hkn : K.succ ≤ n := le_trans (Nat.le_add_left _ _) hn
  have hle : M ≤ n - K.succ := by
    have h' : M + K.succ ≤ n - K.succ + K.succ := by
      simpa [Nat.sub_add_cancel hkn] using hn
    exact Nat.le_of_add_le_add_right h'
  have hdist : dist (x ((n - K.succ) + K.succ)) p < ε := hM hle
  simpa [Nat.sub_add_cancel hkn] using hdist

/-- The distance between evaluations of two continuous functions is controlled
by their supremum distance. -/
lemma dist_eval_le_sup {a b : ℝ} (h k : C(Set.Icc a b, ℝ)) (x : Set.Icc a b) :
    dist (h x) (k x) ≤ dist h k := by
  have hle := ContinuousMap.norm_coe_le_norm (f := h - k) x
  simpa [dist_eq_norm, sub_eq_add_neg] using hle

/-- A uniform pointwise bound on two continuous functions gives a bound on
their supremum distance. -/
lemma sup_norm_le_of_pointwise {a b : ℝ} (h k : C(Set.Icc a b, ℝ)) {ε : ℝ}
    (hε : 0 ≤ ε) (hpoint : ∀ x : Set.Icc a b, dist (h x) (k x) ≤ ε) :
    dist h k ≤ ε := by
  have hpoint' : ∀ x : Set.Icc a b, ‖(h - k) x‖ ≤ ε := by
    intro x
    simpa [dist_eq_norm, sub_eq_add_neg] using hpoint x
  have hnorm : ‖h - k‖ ≤ ε :=
    (ContinuousMap.norm_le (f := h - k) hε).2 hpoint'
  simpa [dist_eq_norm] using hnorm

/-- Example 7.3.7. For continuous real-valued functions on a closed interval
`[a, b]` endowed with the uniform (supremum) norm, convergence of a sequence in
the metric space sense is the same as uniform convergence. -/
theorem uniformConvergence_iff_convergesInSupMetric {a b : ℝ}
    (f : MetricSequence C(Set.Icc a b, ℝ)) (g : C(Set.Icc a b, ℝ)) :
    (∀ ε > 0, ∃ M : ℕ, ∀ ⦃n⦄, M ≤ n → ∀ x : Set.Icc a b,
      dist (f n x) (g x) < ε) ↔
      MetricConvergesTo (X := C(Set.Icc a b, ℝ)) f g := by
  constructor
  · intro h ε hεpos
    obtain ⟨M, hM⟩ := h (ε / 2) (half_pos hεpos)
    refine ⟨M, ?_⟩
    intro n hn
    have hpoint :
        ∀ x : Set.Icc a b, dist (f n x) (g x) ≤ ε / 2 := by
      intro x
      have hx := hM (n := n) hn x
      exact le_of_lt hx
    have hdist : dist (f n) g ≤ ε / 2 :=
      sup_norm_le_of_pointwise (h := f n) (k := g)
        (le_of_lt (half_pos hεpos)) hpoint
    have hhalf : ε / 2 < ε := half_lt_self hεpos
    exact lt_of_le_of_lt hdist hhalf
  · intro h ε hεpos
    obtain ⟨M, hM⟩ := h ε hεpos
    refine ⟨M, ?_⟩
    intro n hn x
    have hdist : dist (f n) g < ε := hM (n := n) hn
    have hle : dist (f n x) (g x) ≤ dist (f n) g :=
      dist_eval_le_sup (h := f n) (k := g) x
    exact lt_of_le_of_lt hle hdist

/-- Proposition 7.3.9. A sequence in Euclidean space `ℝⁿ` converges if and
only if each coordinate sequence converges, and the limit vector has the
coordinatewise limits. -/
theorem metricConvergesTo_euclidean_iff_coordinates {n : ℕ}
    (x : MetricSequence (EuclideanSpace ℝ (Fin n)))
    (l : EuclideanSpace ℝ (Fin n)) :
    MetricConvergesTo (X := EuclideanSpace ℝ (Fin n)) x l ↔
      ∀ k : Fin n, MetricConvergesTo (X := ℝ) (fun m => x m k) (l k) := by
  classical
  let hHomeo :=
    PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)
  constructor
  · intro hx k
    have hx' :
        Filter.Tendsto x Filter.atTop (nhds l) :=
      (metricConvergesTo_iff_tendsto (X := EuclideanSpace ℝ (Fin n)) x l).1 hx
    have hxfun :
        Filter.Tendsto (fun m => hHomeo (x m)) Filter.atTop (nhds (hHomeo l)) :=
      (hHomeo.continuous.continuousAt.tendsto.comp hx')
    have hcoordfun :
        ∀ k : Fin n,
          Filter.Tendsto (fun m => hHomeo (x m) k) Filter.atTop
            (nhds ((hHomeo l) k)) :=
      (tendsto_pi_nhds).1 hxfun
    have hcoord :
        ∀ k : Fin n,
          Filter.Tendsto (fun m => x m k) Filter.atTop (nhds (l k)) :=
      fun k => by
        simpa [hHomeo] using hcoordfun k
    exact
      (metricConvergesTo_iff_tendsto (X := ℝ) (fun m => x m k) (l k)).2 (hcoord k)
  · intro h
    have hcoord :
        ∀ k : Fin n,
          Filter.Tendsto (fun m => x m k) Filter.atTop (nhds (l k)) :=
      fun k =>
        (metricConvergesTo_iff_tendsto (X := ℝ) (fun m => x m k) (l k)).1 (h k)
    have hxfun :
        Filter.Tendsto (fun m => hHomeo (x m)) Filter.atTop (nhds (hHomeo l)) :=
      (tendsto_pi_nhds).2 (by
        intro k
        simpa [hHomeo] using hcoord k)
    have hx : Filter.Tendsto x Filter.atTop (nhds l) := by
      have := (hHomeo.symm.continuous.continuousAt.tendsto.comp hxfun)
      simpa [hHomeo] using this
    exact
      (metricConvergesTo_iff_tendsto (X := EuclideanSpace ℝ (Fin n)) x l).2 hx

/-- A sequence in `ℝⁿ` converges exactly when every coordinate sequence
converges. In this case the limit is the vector of the coordinate limits. -/
theorem convergent_euclidean_iff_coordinates {n : ℕ}
    (x : MetricSequence (EuclideanSpace ℝ (Fin n))) :
    MetricConvergentSequence (X := EuclideanSpace ℝ (Fin n)) x ↔
      ∀ k : Fin n, MetricConvergentSequence (X := ℝ) (fun m => x m k) := by
  constructor
  · intro hx k
    rcases hx with ⟨l, hl⟩
    have hcoord :
        ∀ k : Fin n, MetricConvergesTo (X := ℝ) (fun m => x m k) (l k) :=
      (metricConvergesTo_euclidean_iff_coordinates (x := x) (l := l)).1 hl
    exact ⟨l k, hcoord k⟩
  · intro hx
    classical
    let l : EuclideanSpace ℝ (Fin n) :=
      (WithLp.equiv (2 : ENNReal) (Fin n → ℝ)).symm
        (fun k => Classical.choose (hx k))
    have hcoord :
        ∀ k : Fin n, MetricConvergesTo (X := ℝ) (fun m => x m k) (l k) :=
      by
        intro k
        simpa [l] using Classical.choose_spec (hx k)
    refine ⟨l, ?_⟩
    exact
      (metricConvergesTo_euclidean_iff_coordinates (x := x) (l := l)).2 hcoord

/-- Convergence of complex numbers is equivalent to convergence of the
real and imaginary parts. -/
lemma tendsto_complex_iff_real_im (z : MetricSequence ℂ) (x y : ℝ) :
    Filter.Tendsto z Filter.atTop (nhds (x + y * Complex.I)) ↔
      Filter.Tendsto (fun n => (z n).re) Filter.atTop (nhds x) ∧
        Filter.Tendsto (fun n => (z n).im) Filter.atTop (nhds y) := by
  constructor
  · intro hz
    have hz' :
        Filter.Tendsto (fun n => Complex.equivRealProdCLM (z n))
          Filter.atTop (nhds (Complex.equivRealProdCLM (x + y * Complex.I))) :=
      (Complex.equivRealProdCLM.continuous.tendsto (x + y * Complex.I)).comp hz
    have hprod :=
      (Prod.tendsto_iff
        (seq := fun n => Complex.equivRealProdCLM (z n))
        (f := Filter.atTop)
        (p := Complex.equivRealProdCLM (x + y * Complex.I))).mp hz'
    constructor
    · simpa using hprod.1
    · simpa using hprod.2
  · rintro ⟨hre, him⟩
    have hprod :
        Filter.Tendsto (fun n => Complex.equivRealProdCLM (z n))
          Filter.atTop (nhds (x, y)) :=
      (Prod.tendsto_iff
        (seq := fun n => Complex.equivRealProdCLM (z n))
        (f := Filter.atTop)
        (p := (x, y))).mpr ⟨hre, him⟩
    have hz :
        Filter.Tendsto (fun n => Complex.equivRealProdCLM.symm
          (Complex.equivRealProdCLM (z n))) Filter.atTop
          (nhds (Complex.equivRealProdCLM.symm (x, y))) :=
      (Complex.equivRealProdCLM.symm.continuous.tendsto (x, y)).comp hprod
    simpa [Complex.equivRealProdCLM_symm_apply] using hz

/-- Example 7.3.10. In the complex plane viewed as `ℝ²`, a sequence
`zₙ = xₙ + i yₙ` converges to `x + i y` if and only if the real parts converge
to `x` and the imaginary parts converge to `y`. -/
theorem metricConvergesTo_complex_iff_re_im (z : MetricSequence ℂ) (x y : ℝ) :
    MetricConvergesTo (X := ℂ) z (x + y * Complex.I) ↔
      MetricConvergesTo (X := ℝ) (fun n => (z n).re) x ∧
        MetricConvergesTo (X := ℝ) (fun n => (z n).im) y := by
  constructor
  · intro hz
    have ht :
        Filter.Tendsto z Filter.atTop (nhds (x + y * Complex.I)) :=
      (metricConvergesTo_iff_tendsto (X := ℂ) z (x + y * Complex.I)).1 hz
    have hproj := (tendsto_complex_iff_real_im (z := z) x y).1 ht
    constructor
    · exact
        (metricConvergesTo_iff_tendsto (X := ℝ) (fun n => (z n).re) x).2 hproj.1
    · exact
        (metricConvergesTo_iff_tendsto (X := ℝ) (fun n => (z n).im) y).2 hproj.2
  · rintro ⟨hre, him⟩
    have hre' :
        Filter.Tendsto (fun n => (z n).re) Filter.atTop (nhds x) :=
      (metricConvergesTo_iff_tendsto (X := ℝ) (fun n => (z n).re) x).1 hre
    have him' :
        Filter.Tendsto (fun n => (z n).im) Filter.atTop (nhds y) :=
      (metricConvergesTo_iff_tendsto (X := ℝ) (fun n => (z n).im) y).1 him
    have ht :
        Filter.Tendsto z Filter.atTop (nhds (x + y * Complex.I)) :=
      (tendsto_complex_iff_real_im (z := z) x y).2 ⟨hre', him'⟩
    exact (metricConvergesTo_iff_tendsto (X := ℂ) z (x + y * Complex.I)).2 ht

lemma metricConvergesTo_eventually_mem_open {x : MetricSequence X} {p : X} {U : Set X}
    (hx : MetricConvergesTo (X := X) x p) (hUopen : IsOpen U) (hpU : p ∈ U) :
    ∃ M : ℕ, ∀ ⦃n⦄, M ≤ n → x n ∈ U := by
  have ht : Filter.Tendsto x Filter.atTop (nhds p) :=
    (metricConvergesTo_iff_tendsto (X := X) x p).1 hx
  have hmem : U ∈ nhds p := hUopen.mem_nhds hpU
  have hEV : Filter.Eventually (fun n => x n ∈ U) Filter.atTop :=
    ht.eventually hmem
  rcases Filter.eventually_atTop.1 hEV with ⟨M, hM⟩
  exact ⟨M, by intro n hn; exact hM n hn⟩

lemma tendsto_of_eventually_mem_open {x : MetricSequence X} {p : X}
    (hx : ∀ {U : Set X}, IsOpen U → p ∈ U →
      ∃ M : ℕ, ∀ ⦃n⦄, M ≤ n → x n ∈ U) :
    Filter.Tendsto x Filter.atTop (nhds p) := by
  refine Filter.tendsto_def.2 ?_
  intro s hs
  rcases mem_nhds_iff.1 hs with ⟨U, hUsubset, hUopen, hpU⟩
  obtain ⟨M, hM⟩ := hx hUopen hpU
  refine Filter.eventually_atTop.2 ?_
  refine ⟨M, ?_⟩
  intro n hn
  exact hUsubset (hM hn)

/-- Proposition 7.3.11. A sequence in a metric space converges to `p` exactly
when eventually all of its terms lie in every open neighborhood of `p`. -/
theorem metricConvergesTo_iff_eventually_mem_nhds {x : MetricSequence X} {p : X} :
    MetricConvergesTo (X := X) x p ↔
      ∀ {U : Set X}, IsOpen U → p ∈ U →
        ∃ M : ℕ, ∀ ⦃n⦄, M ≤ n → x n ∈ U := by
  constructor
  · intro hx U hUopen hpU
    exact
      metricConvergesTo_eventually_mem_open (X := X) (x := x) (p := p)
        (U := U) hx hUopen hpU
  · intro hx
    have ht : Filter.Tendsto x Filter.atTop (nhds p) :=
      tendsto_of_eventually_mem_open (X := X) (x := x) (p := p) hx
    exact (metricConvergesTo_iff_tendsto (X := X) x p).2 ht

/-- Proposition 7.3.12. In a metric space, a closed set contains the limit of
a convergent sequence of its points. -/
theorem mem_closed_of_converges {X : Type u} [PseudoMetricSpace X] {E : Set X}
    (hE : IsClosed E) {x : MetricSequence X} (hx : ∀ n, x n ∈ E) {p : X}
    (hxlim : MetricConvergesTo (X := X) x p) : p ∈ E := by
  classical
  by_contra hp
  have hOpen : IsOpen (Eᶜ) := hE.isOpen_compl
  rcases
      metricConvergesTo_eventually_mem_open (X := X) (x := x) (p := p) (U := Eᶜ)
        hxlim hOpen (by simpa using hp) with
    ⟨M, hM⟩
  have hxc : x M ∉ E := by
    have h := hM (n := M) le_rfl
    simpa using h
  exact hxc (hx M)

/-- Proposition 7.3.13. A point lies in the closure of a set in a metric space
exactly when it is the limit of a sequence of points from that set. -/
theorem mem_closure_iff_metricConvergesTo_seq {X : Type u} [PseudoMetricSpace X]
    {A : Set X} {p : X} :
    p ∈ closure A ↔ ∃ x : MetricSequence X,
      (∀ n, x n ∈ A) ∧ MetricConvergesTo (X := X) x p := by
  constructor
  · intro hp
    classical
    -- choose a point in `A` within distance `1/(n+1)` of `p` for each `n`
    have hx :
        ∀ n : ℕ, ∃ y : X, y ∈ A ∧ dist y p < (1 : ℝ) / (n.succ : ℝ) := by
      intro n
      have hpos : 0 < (1 : ℝ) / (n.succ : ℝ) :=
        one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n)
      rcases (Metric.mem_closure_iff.mp hp) ((1 : ℝ) / (n.succ : ℝ)) hpos with
        ⟨y, hyA, hylt⟩
      exact ⟨y, hyA, by simpa [dist_comm] using hylt⟩
    choose x hxA hxlt using hx
    -- the distance bound forces convergence to `p`
    have hxlim : MetricConvergesTo (X := X) x p := by
      intro ε hεpos
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt hεpos
      refine ⟨M, ?_⟩
      intro n hn
      have hle : (1 : ℝ) / (n.succ : ℝ) ≤ (1 : ℝ) / (M.succ : ℝ) := by
        have hle_nat : M.succ ≤ n.succ := Nat.succ_le_succ hn
        have hpos : (0 : ℝ) < (M.succ : ℝ) := by exact_mod_cast Nat.succ_pos M
        have hle' : (M.succ : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast hle_nat
        exact one_div_le_one_div_of_le hpos hle'
      have hlt : dist (x n) p < (1 : ℝ) / (M.succ : ℝ) :=
        lt_of_lt_of_le (hxlt n) hle
      have hM' : (1 : ℝ) / (M.succ : ℝ) < ε := by
        simpa [Nat.succ_eq_add_one] using hM
      exact lt_trans hlt hM'
    exact ⟨x, hxA, hxlim⟩
  · rintro ⟨x, hxA, hxlim⟩
    have hxclosure : ∀ n, x n ∈ closure A := fun n => subset_closure (hxA n)
    have hclosed : IsClosed (closure A) := isClosed_closure
    exact
      mem_closed_of_converges (X := X) (E := closure A) hclosed hxclosure hxlim

end

end Section03
end Chap07
