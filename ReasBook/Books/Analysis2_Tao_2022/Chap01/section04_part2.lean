/-
Authors: Zichen Wang, Wanli Ma, Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap01.section04_part1

section Chap01
section Section04

open Filter

/-- Helper for Theorem 1.4: the chosen subsequence converges to the diagonal class. -/
lemma helperForTheorem_1_4_subseq_tendsto (X : Type u) [MetricSpace X]
    {u : ℕ → CompletionViaFormalLimits X} {m : ℕ → ℕ}
    {x : ℕ → FormalLimit X}
    (hx : ∀ n, u (m n) = Quotient.mk (FormalLimitSetoid (X := X)) (x n))
    {k : ℕ → ℕ} (hkmono : Monotone k)
    (hA : ∀ n, ∀ j ≥ k n,
      dist ((x n).1 j) ((x (n + 1)).1 j) < (1 / 2 : ℝ) ^ (n + 2))
    (hB : ∀ n, ∀ j ≥ k n,
      dist ((x (n + 1)).1 (k n)) ((x (n + 1)).1 j) < (1 / 2 : ℝ) ^ (n + 2))
    (hy : CauchySeq (fun n => (x n).1 (k n))) :
    Tendsto (fun n => u (m n)) atTop
      (nhds
        (Quotient.mk (FormalLimitSetoid (X := X))
          ⟨fun n => (x n).1 (k n), hy⟩)) := by
  classical
  let y : ℕ → X := fun n => (x n).1 (k n)
  let L : CompletionViaFormalLimits X :=
    Quotient.mk (FormalLimitSetoid (X := X)) ⟨y, hy⟩
  have hy' : CauchySeq y := hy
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hε8 : 0 < ε / 8 := by
    linarith
  rcases helperForTheorem_1_4_pow_eventually_lt (ε / 8) hε8 with ⟨N1, hN1⟩
  have hyc' := (Metric.cauchySeq_iff).1 hy'
  rcases hyc' (ε / 8) hε8 with ⟨N2, hN2⟩
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  let J := max (k n) N2
  have hJk : k n ≤ J := le_max_left _ _
  have hJN2 : N2 ≤ J := le_max_right _ _
  have hbound : ∀ j ≥ J, dist ((x n).1 j) (y j) < ε / 2 := by
    intro j hj
    have hjk : k n ≤ j := le_trans hJk hj
    have hjN2 : N2 ≤ j := le_trans hJN2 hj
    have hrn : (1 / 2 : ℝ) ^ (n + 2) < ε / 8 := hN1 n hn1
    have hA' :
        dist ((x n).1 j) ((x (n + 1)).1 j) < (1 / 2 : ℝ) ^ (n + 2) := hA n j hjk
    have hB1 :
        dist ((x (n + 1)).1 j) ((x (n + 1)).1 (k n)) < (1 / 2 : ℝ) ^ (n + 2) := by
      simpa [dist_comm] using hB n j hjk
    have hkn : k n ≤ k (n + 1) := hkmono (Nat.le_succ n)
    have hB2 :
        dist ((x (n + 1)).1 (k n)) (y (n + 1)) < (1 / 2 : ℝ) ^ (n + 2) := by
      simpa [y] using hB n (k (n + 1)) hkn
    have hY :
        dist (y (n + 1)) (y j) < ε / 8 := by
      have hn2' : N2 ≤ n + 1 := le_trans hn2 (Nat.le_succ n)
      exact hN2 (n + 1) hn2' j hjN2
    have htri1 :
        dist ((x n).1 j) (y j) ≤
          dist ((x n).1 j) ((x (n + 1)).1 j) +
            dist ((x (n + 1)).1 j) (y j) :=
      dist_triangle _ _ _
    have htri2 :
        dist ((x (n + 1)).1 j) (y j) ≤
          dist ((x (n + 1)).1 j) ((x (n + 1)).1 (k n)) +
            dist ((x (n + 1)).1 (k n)) (y j) :=
      dist_triangle _ _ _
    have htri3 :
        dist ((x (n + 1)).1 (k n)) (y j) ≤
          dist ((x (n + 1)).1 (k n)) (y (n + 1)) +
            dist (y (n + 1)) (y j) :=
      dist_triangle _ _ _
    have htri_all :
        dist ((x n).1 j) (y j) ≤
          dist ((x n).1 j) ((x (n + 1)).1 j) +
            dist ((x (n + 1)).1 j) ((x (n + 1)).1 (k n)) +
              dist ((x (n + 1)).1 (k n)) (y (n + 1)) +
                dist (y (n + 1)) (y j) := by
      linarith [htri1, htri2, htri3]
    have hsum :
        dist ((x n).1 j) (y j) <
          (1 / 2 : ℝ) ^ (n + 2) +
            (1 / 2 : ℝ) ^ (n + 2) +
              (1 / 2 : ℝ) ^ (n + 2) + ε / 8 := by
      have hsum' :
          dist ((x n).1 j) ((x (n + 1)).1 j) +
              dist ((x (n + 1)).1 j) ((x (n + 1)).1 (k n)) +
                dist ((x (n + 1)).1 (k n)) (y (n + 1)) +
                  dist (y (n + 1)) (y j) <
            (1 / 2 : ℝ) ^ (n + 2) +
              (1 / 2 : ℝ) ^ (n + 2) +
                (1 / 2 : ℝ) ^ (n + 2) + ε / 8 := by
        linarith [hA', hB1, hB2, hY]
      exact lt_of_le_of_lt htri_all hsum'
    have hfinal : dist ((x n).1 j) (y j) < ε / 2 := by
      linarith [hsum, hrn]
    exact hfinal
  have hle : ∀ᶠ j in atTop, dist ((x n).1 j) (y j) ≤ ε / 2 := by
    refine (eventually_atTop.2 ?_)
    refine ⟨J, ?_⟩
    intro j hj
    exact le_of_lt (hbound j hj)
  have hlim :
      Tendsto (fun j => dist ((x n).1 j) (y j)) atTop
        (nhds (helperForProposition_1_24_formalLimitDist (X := X) (x n) ⟨y, hy⟩)) := by
    exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) (x n) ⟨y, hy⟩
  have hle' :
      helperForProposition_1_24_formalLimitDist (X := X) (x n) ⟨y, hy⟩ ≤ ε / 2 := by
    exact tendsto_le_of_eventuallyLE hlim (tendsto_const_nhds) hle
  have hdist_le :
      completionViaFormalLimitsDist X (u (m n)) L ≤ ε / 2 := by
    simpa [completionViaFormalLimitsDist, hx n, L, y] using hle'
  have hdist_lt : completionViaFormalLimitsDist X (u (m n)) L < ε := by
    have hhalf : ε / 2 < ε := by
      linarith
    exact lt_of_le_of_lt hdist_le hhalf
  simpa [L] using hdist_lt

/-- Theorem 1.4: Let `(X,d)` be a metric space. Define `Xbar` as the set of equivalence classes
of Cauchy sequences in `X` under `(x_n) ~ (y_n)` iff `d(x_n,y_n) -> 0` as `n -> infinity`. For
classes `[(x_n)], [(y_n)]` define `d_{Xbar}([(x_n)],[(y_n)]) := lim_{n -> infinity} d(x_n,y_n)`,
which is well-defined. Then `(Xbar, d_{Xbar})` is complete. -/
theorem completionViaFormalLimits_completeSpace (X : Type u) [MetricSpace X] :
    CompleteSpace (CompletionViaFormalLimits X) := by
  classical
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  rcases helperForTheorem_1_4_cauchySeq_subseq_geometric (X := X) u hu with ⟨m, hm, hdist⟩
  rcases helperForTheorem_1_4_chooseRepresentatives (X := X) (u := fun n => u (m n))
      with ⟨x, hx⟩
  rcases helperForTheorem_1_4_diagonal_index (X := X) (u := u) (m := m) (x := x) hx hdist
      with ⟨k, hkmono, hA, hB⟩
  have hy : CauchySeq (fun n => (x n).1 (k n)) :=
    helperForTheorem_1_4_diagonal_cauchy (X := X) (x := x) (k := k) hkmono hA hB
  let L : CompletionViaFormalLimits X :=
    Quotient.mk (FormalLimitSetoid (X := X)) ⟨fun n => (x n).1 (k n), hy⟩
  have hsub :
      Tendsto (fun n => u (m n)) atTop (nhds L) := by
    simpa [L] using
      (helperForTheorem_1_4_subseq_tendsto (X := X) (u := u) (m := m)
        (x := x) hx (k := k) hkmono hA hB hy)
  have hfull : Tendsto u atTop (nhds L) :=
    helperForTheorem_1_4_tendsto_of_cauchy_of_subseq (u := u) hu (m := m) hm hsub
  exact ⟨L, hfull⟩

/-- The constant sequence in a metric space is Cauchy. -/
lemma cauchySeq_const' {X : Type u} [MetricSpace X] (x : X) :
    CauchySeq (fun _ : ℕ => x) := by
  simpa using (cauchySeq_const (x := x) : CauchySeq (fun _ : ℕ => x))

/-- The canonical map `X →` formal-limit completion, sending `x` to the constant sequence. -/
def completionViaFormalLimitsIota (X : Type u) [MetricSpace X] :
    X → CompletionViaFormalLimits X :=
  fun x =>
    Quotient.mk (FormalLimitSetoid (X := X))
      ⟨fun _ : ℕ => x, cauchySeq_const' (X := X) x⟩

/-- Proposition 1.25: Let `(X,d)` be a metric space, let `X̄` be the set of equivalence classes of
Cauchy sequences in `X`, and define `d_{X̄}(LIM x_n, LIM y_n) := lim_{n→∞} d(x_n,y_n)`. Define
`iota : X → X̄` by sending `x` to the equivalence class of the constant sequence. (i) For all
`x, y ∈ X`, one has `x = y` iff `iota x = iota y`. (ii) For all `x, y ∈ X`, one has
`d(x,y) = d_{X̄}(iota x, iota y)`. In particular, `iota` is an isometric embedding. -/
theorem completionViaFormalLimitsIota_props (X : Type u) [MetricSpace X] :
    (∀ x y : X, x = y ↔ completionViaFormalLimitsIota X x = completionViaFormalLimitsIota X y) ∧
    (∀ x y : X,
      dist x y =
        completionViaFormalLimitsDist X (completionViaFormalLimitsIota X x)
          (completionViaFormalLimitsIota X y)) ∧
    Isometry (completionViaFormalLimitsIota X) := by
  refine And.intro ?_ ?_
  · intro x y
    constructor
    · intro hxy
      exact congrArg (completionViaFormalLimitsIota X) hxy
    · intro hxy
      have hxy' :
          Quotient.mk (FormalLimitSetoid (X := X))
              ⟨fun _ : ℕ => x, cauchySeq_const' (X := X) x⟩ =
            Quotient.mk (FormalLimitSetoid (X := X))
              ⟨fun _ : ℕ => y, cauchySeq_const' (X := X) y⟩ := by
        simpa [completionViaFormalLimitsIota] using hxy
      have hrel :
          FormalLimitRel (X := X)
              ⟨fun _ : ℕ => x, cauchySeq_const' (X := X) x⟩
              ⟨fun _ : ℕ => y, cauchySeq_const' (X := X) y⟩ :=
        Quotient.exact hxy'
      have hlim : Tendsto (fun _ : ℕ => dist x y) atTop (nhds 0) := by
        simpa [FormalLimitRel] using hrel
      have hconst :
          Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)) := by
        simpa using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)))
      have hzero : dist x y = 0 :=
        tendsto_nhds_unique hconst hlim
      exact (dist_eq_zero).1 hzero
  · refine And.intro ?_ ?_
    · intro x y
      have hcy : CauchySeq (fun _ : ℕ => dist x y) := by
        simpa using
          (cauchySeq_const (x := dist x y) : CauchySeq (fun _ : ℕ => dist x y))
      have hlim :
          Tendsto (fun _ : ℕ => dist x y) atTop
            (nhds (limUnder atTop (fun _ : ℕ => dist x y))) := by
        simpa using (CauchySeq.tendsto_limUnder hcy)
      have hconst :
          Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)) := by
        simpa using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)))
      have hlim_eq : limUnder atTop (fun _ : ℕ => dist x y) = dist x y :=
        tendsto_nhds_unique hlim hconst
      have hdist_eq :
          helperForProposition_1_24_formalLimitDist (X := X)
              ⟨fun _ : ℕ => x, cauchySeq_const' (X := X) x⟩
              ⟨fun _ : ℕ => y, cauchySeq_const' (X := X) y⟩ = dist x y := by
        simpa [helperForProposition_1_24_formalLimitDist] using hlim_eq
      simpa [completionViaFormalLimitsDist, completionViaFormalLimitsIota, hdist_eq]
    · refine (isometry_iff_dist_eq).2 ?_
      intro x y
      have hcy : CauchySeq (fun _ : ℕ => dist x y) := by
        simpa using
          (cauchySeq_const (x := dist x y) : CauchySeq (fun _ : ℕ => dist x y))
      have hlim :
          Tendsto (fun _ : ℕ => dist x y) atTop
            (nhds (limUnder atTop (fun _ : ℕ => dist x y))) := by
        simpa using (CauchySeq.tendsto_limUnder hcy)
      have hconst :
          Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)) := by
        simpa using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)))
      have hlim_eq : limUnder atTop (fun _ : ℕ => dist x y) = dist x y :=
        tendsto_nhds_unique hlim hconst
      have hdist_eq :
          helperForProposition_1_24_formalLimitDist (X := X)
              ⟨fun _ : ℕ => x, cauchySeq_const' (X := X) x⟩
              ⟨fun _ : ℕ => y, cauchySeq_const' (X := X) y⟩ = dist x y := by
        simpa [helperForProposition_1_24_formalLimitDist] using hlim_eq
      have hdist :
          dist x y =
            completionViaFormalLimitsDist X (completionViaFormalLimitsIota X x)
              (completionViaFormalLimitsIota X y) := by
        simpa [completionViaFormalLimitsDist, completionViaFormalLimitsIota, hdist_eq]
      simpa using hdist.symm

/-- Equality in `X` is equivalent to equality in the formal completion via `iota`. -/
lemma completionViaFormalLimitsIota_eq_iff {X : Type u} [MetricSpace X] (x y : X) :
    x = y ↔ completionViaFormalLimitsIota X x = completionViaFormalLimitsIota X y := by
  constructor
  · intro hxy
    exact congrArg (completionViaFormalLimitsIota X) hxy
  · intro hxy
    have hxy' :
        Quotient.mk (FormalLimitSetoid (X := X))
            ⟨fun _ : ℕ => x, cauchySeq_const' (X := X) x⟩ =
          Quotient.mk (FormalLimitSetoid (X := X))
            ⟨fun _ : ℕ => y, cauchySeq_const' (X := X) y⟩ := by
      simpa [completionViaFormalLimitsIota] using hxy
    have hrel :
        FormalLimitRel (X := X)
            ⟨fun _ : ℕ => x, cauchySeq_const' (X := X) x⟩
            ⟨fun _ : ℕ => y, cauchySeq_const' (X := X) y⟩ :=
      Quotient.exact hxy'
    have hlim : Tendsto (fun _ : ℕ => dist x y) atTop (nhds 0) := by
      simpa [FormalLimitRel] using hrel
    have hconst :
        Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)) := by
      simpa using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)))
    have hzero : dist x y = 0 :=
      tendsto_nhds_unique hconst hlim
    exact (dist_eq_zero).1 hzero

/-- The canonical map into the formal completion preserves distances. -/
lemma completionViaFormalLimitsIota_dist {X : Type u} [MetricSpace X] (x y : X) :
    dist x y =
      completionViaFormalLimitsDist X (completionViaFormalLimitsIota X x)
        (completionViaFormalLimitsIota X y) := by
  have hcy : CauchySeq (fun _ : ℕ => dist x y) := by
    simpa using
      (cauchySeq_const (x := dist x y) : CauchySeq (fun _ : ℕ => dist x y))
  have hlim :
      Tendsto (fun _ : ℕ => dist x y) atTop
        (nhds (limUnder atTop (fun _ : ℕ => dist x y))) := by
    simpa using (CauchySeq.tendsto_limUnder hcy)
  have hconst :
      Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => dist x y) atTop (nhds (dist x y)))
  have hlim_eq : limUnder atTop (fun _ : ℕ => dist x y) = dist x y :=
    tendsto_nhds_unique hlim hconst
  have hdist_eq :
      helperForProposition_1_24_formalLimitDist (X := X)
          ⟨fun _ : ℕ => x, cauchySeq_const' (X := X) x⟩
          ⟨fun _ : ℕ => y, cauchySeq_const' (X := X) y⟩ = dist x y := by
    simpa [helperForProposition_1_24_formalLimitDist] using hlim_eq
  simpa [completionViaFormalLimitsDist, completionViaFormalLimitsIota, hdist_eq]

/-- The canonical embedding into the formal completion is an isometry. -/
theorem completionViaFormalLimitsIota_isometry {X : Type u} [MetricSpace X] :
    Isometry (completionViaFormalLimitsIota X) := by
  refine (isometry_iff_dist_eq).2 ?_
  intro x y
  simpa using (completionViaFormalLimitsIota_dist (X := X) x y).symm

/-- Helper for Proposition 1.26: each formal limit class lies in the closure of the canonical image of `X`. -/
lemma helperForProposition_1_26_mk_mem_closure_range_iota {X : Type u} [MetricSpace X]
    (x : FormalLimit X) :
    Quotient.mk (FormalLimitSetoid (X := X)) x ∈
      closure (Set.range (completionViaFormalLimitsIota X)) := by
  classical
  let q : CompletionViaFormalLimits X :=
    Quotient.mk (FormalLimitSetoid (X := X)) x
  have hq : q ∈ closure (Set.range (completionViaFormalLimitsIota X)) := by
    refine (Metric.mem_closure_iff).2 ?_
    intro ε hε
    rcases (Metric.cauchySeq_iff).1 x.2 with hx
    have hε' : 0 < ε / 2 := by
      linarith
    rcases hx (ε / 2) hε' with ⟨N, hN⟩
    refine ⟨completionViaFormalLimitsIota X (x.1 N), ?_, ?_⟩
    · exact ⟨x.1 N, rfl⟩
    let zN : FormalLimit X :=
      ⟨fun _ : ℕ => x.1 N, cauchySeq_const' (X := X) (x.1 N)⟩
    have hle : ∀ᶠ n in atTop, dist (x.1 n) (x.1 N) ≤ ε / 2 := by
      refine (eventually_atTop.2 ?_)
      refine ⟨N, ?_⟩
      intro n hn
      have hdist' : dist (x.1 N) (x.1 n) < ε / 2 := hN N (le_rfl) n hn
      have hdist : dist (x.1 n) (x.1 N) < ε / 2 := by
        simpa [dist_comm] using hdist'
      exact le_of_lt hdist
    have hlim :
        Tendsto (fun n : ℕ => dist (x.1 n) (x.1 N)) atTop
          (nhds (helperForProposition_1_24_formalLimitDist (X := X) x zN)) := by
      exact helperForProposition_1_24_formalLimitDist_tendsto (X := X) x zN
    have hle' :
        helperForProposition_1_24_formalLimitDist (X := X) x zN ≤ ε / 2 := by
      exact tendsto_le_of_eventuallyLE hlim (tendsto_const_nhds) hle
    have hdist_le :
        completionViaFormalLimitsDist X q
          (completionViaFormalLimitsIota X (x.1 N)) ≤ ε / 2 := by
      simpa [completionViaFormalLimitsDist, completionViaFormalLimitsIota, zN, q] using hle'
    have hhalf : ε / 2 < ε := by
      linarith
    have hdist_lt :
        completionViaFormalLimitsDist X q
          (completionViaFormalLimitsIota X (x.1 N)) < ε := by
      exact lt_of_le_of_lt hdist_le hhalf
    change
        completionViaFormalLimitsDist X q
          (completionViaFormalLimitsIota X (x.1 N)) < ε
    exact hdist_lt
  simpa [q] using hq

/-- Helper for Proposition 1.26: the canonical map into the completion has dense range. -/
theorem helperForProposition_1_26_denseRange_iota (X : Type u) [MetricSpace X] :
    DenseRange (completionViaFormalLimitsIota X) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact helperForProposition_1_26_mk_mem_closure_range_iota (X := X) x

/-- Proposition 1.26: Let `(X,d)` be a metric space. Let `(Xbar, d_{Xbar})` be the completion of
`X` constructed by formal limits, and identify `X` with its canonical image in `Xbar`. Then
`Xbar` is the closure of `X` in `Xbar`, i.e. `Xbar = closure_X^{Xbar}`. -/
/- The formal-limit completion is the closure of the canonical image of `X`. -/
theorem completionViaFormalLimits_closure_range (X : Type u) [MetricSpace X] :
    closure (Set.range (completionViaFormalLimitsIota X)) =
      (Set.univ : Set (CompletionViaFormalLimits X)) := by
  have hdense : DenseRange (completionViaFormalLimitsIota X) :=
    helperForProposition_1_26_denseRange_iota (X := X)
  simpa using (DenseRange.closure_range hdense)

/-- Helper for Proposition 1.27: convergence implies distances to the limit tend to zero. -/
lemma helperForProposition_1_27_tendsto_dist_to_limit {X : Type u} [MetricSpace X] (x : ℕ → X)
    {x0 : X} (hlim : Tendsto x atTop (nhds x0)) :
    Tendsto (fun n => dist (x n) x0) atTop (nhds 0) := by
  simpa using
    (tendsto_iff_dist_tendsto_zero (f := x) (x := atTop) (a := x0)).1 hlim

/-- Helper for Proposition 1.27: relate a convergent Cauchy sequence to the constant formal limit. -/
lemma helperForProposition_1_27_formalLimitRel_const_of_tendsto {X : Type u} [MetricSpace X]
    (x : ℕ → X) {x0 : X} (hx : CauchySeq x) (hlim : Tendsto x atTop (nhds x0)) :
    FormalLimitRel (X := X) ⟨x, hx⟩
      ⟨fun _ : ℕ => x0, cauchySeq_const' (X := X) x0⟩ := by
  have hdist : Tendsto (fun n => dist (x n) x0) atTop (nhds 0) :=
    helperForProposition_1_27_tendsto_dist_to_limit (x := x) (x0 := x0) hlim
  simpa [FormalLimitRel] using hdist

/-- Proposition 1.27: Let `(X,d)` be a metric space. Let `(Xbar, d_{Xbar})` be the completion of
`X` constructed via formal limits of Cauchy sequences, and identify `X` with its canonical image
in `Xbar`. Let `(x_n)` be a Cauchy sequence in `X` that converges to `x` in `X`. Then the limit of
`(x_n)` in `(Xbar, d_{Xbar})` equals the embedded point `x` in `Xbar`, i.e.
`lim_{n -> infinity} x_n = LIM_{n -> infinity} x_n`.
A convergent Cauchy sequence has formal-limit class equal to the embedded limit. -/
theorem completionViaFormalLimits_limit_eq_iota {X : Type u} [MetricSpace X] (x : ℕ → X) {x0 : X}
    (hx : CauchySeq x) (hlim : Tendsto x atTop (nhds x0)) :
    Quotient.mk (FormalLimitSetoid (X := X)) ⟨x, hx⟩ = completionViaFormalLimitsIota X x0 := by
  have hrel :
      FormalLimitRel (X := X) ⟨x, hx⟩
        ⟨fun _ : ℕ => x0, cauchySeq_const' (X := X) x0⟩ :=
    helperForProposition_1_27_formalLimitRel_const_of_tendsto (x := x) (x0 := x0) hx hlim
  have hquot :
      Quotient.mk (FormalLimitSetoid (X := X)) ⟨x, hx⟩ =
        Quotient.mk (FormalLimitSetoid (X := X))
          ⟨fun _ : ℕ => x0, cauchySeq_const' (X := X) x0⟩ :=
    Quotient.sound hrel
  simpa [completionViaFormalLimitsIota] using hquot

/-- Proposition 1.33 (Complete subspaces are closed): Let `(X,d)` be a metric space and let
`Y ⊆ X` be a subspace. If the metric subspace `(Y, d|_{Y×Y})` is complete, then `Y` is closed
in `X`. -/
/- A complete metric subspace is closed in the ambient space. -/
theorem completeSpace_subtype_isClosed {X : Type*} [MetricSpace X] {Y : Set X} :
    CompleteSpace Y → IsClosed Y := by
  intro hY
  exact (completeSpace_subtype_closed (X := X) (Y := Y)).1 hY

/-- Proposition 1.34 (Closed subspaces of complete spaces are complete): Let `(X,d)` be a
complete metric space and let `Y ⊆ X` be a closed subset. Then the metric subspace
`(Y, d|_{Y×Y})` is complete. -/
/- A closed subset of a complete metric space is complete as a subspace. -/
theorem completeSpace_subtype_of_isClosed {X : Type*} [MetricSpace X] {Y : Set X} :
    CompleteSpace X → IsClosed Y → CompleteSpace Y := by
  intro hX hClosed
  exact (completeSpace_subtype_closed (X := X) (Y := Y)).2 hX hClosed

/-- Proposition 1.37 (Existence of completion): Let `(X,d)` be a metric space. There exists a
complete metric space `(X̄, d̄)` and an isometric embedding `ι : X → X̄` such that `ι(X)` is dense
in `X̄`. -/
theorem exists_completion_metricSpace (X : Type u) [MetricSpace X] :
    ∃ (Xbar : Type u) (inst : MetricSpace Xbar),
      (letI := inst;
        CompleteSpace Xbar ∧
          ∃ iota : X → Xbar, Isometry iota ∧ DenseRange iota) := by
  refine ⟨CompletionViaFormalLimits X, completionViaFormalLimitsMetricSpace (X := X), ?_⟩
  dsimp
  refine And.intro ?_ ?_
  · exact completionViaFormalLimits_completeSpace (X := X)
  · refine ⟨completionViaFormalLimitsIota X, ?_, ?_⟩
    · exact completionViaFormalLimitsIota_isometry (X := X)
    · exact helperForProposition_1_26_denseRange_iota (X := X)

end Section04
end Chap01
