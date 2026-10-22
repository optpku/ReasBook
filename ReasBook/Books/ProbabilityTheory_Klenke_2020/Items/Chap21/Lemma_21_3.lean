/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped NNReal Topology

section RealLocalHolder

variable {I : Set ℝ} {f : I → ℝ} {γ γ' : Set.Ioc (0 : ℝ≥0) 1} {Cε : ℝ≥0} {ε T : ℝ}

-- Proof sketch: around each point, shrink a local `γ`-Hölder neighborhood to diameter at most
-- `1`, then use monotonicity of the power function on `[0,1]` to replace the exponent `γ` by the
-- smaller exponent `γ'`.
/-- First assertion of Lemma 21.3: if `f : I → ℝ` is locally Hölder-continuous of order
`γ ∈ (0,1]`, then it is
also locally Hölder-continuous of every order `γ' ∈ (0, γ)`. -/
theorem locallyHolderWith_subexponent
    (hf : LocallyHolderWith γ f)
    (hγ'γ : (γ' : ℝ≥0) < γ) :
    LocallyHolderWith γ' f := by
  intro x
  -- Proof comment: extract a local `γ`-Hölder ball and shrink it to radius at most `1`,
  -- so the monotonicity lemma for Hölder exponents on bounded sets applies directly.
  rcases hf.exists_holderOnWith_ball x with ⟨ε, hε, C, hC⟩
  let δ : ℝ := min ε 1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hε zero_lt_one
  have hsubset : Metric.ball x δ ⊆ Metric.ball x ε := by
    intro y hy
    exact Metric.mem_ball.2 <| (Metric.mem_ball.1 hy).trans_le (min_le_left _ _)
  have hbounded : Bornology.IsBounded (Metric.ball x δ) := Metric.isBounded_ball
  rcases HolderOnWith.exists_holderOnWith_of_le
      (f := f) (r := (γ : ℝ≥0)) (s := (γ' : ℝ≥0)) (A := Metric.ball x δ)
      ⟨C, hC.mono hsubset⟩ (le_of_lt hγ'γ) hbounded with
    ⟨C', hC'⟩
  refine ⟨Metric.ball x δ, Metric.ball_mem_nhds _ hδ, C', hC'⟩

/-- Helper for Lemma 21.3: a locally Hölder map of positive exponent is continuous. -/
lemma continuous_of_locallyHolderWith
    {X : Type*} {Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {γ : Set.Ioc (0 : ℝ≥0) 1} {f : X → Y}
    (hf : LocallyHolderWith γ f) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases hf x with ⟨s, hs, C, hC⟩
  -- Proof comment: a local Hölder witness is continuous on its witness set, hence continuous at
  -- the center point because the witness set is a neighborhood of that point.
  have hx : x ∈ s := mem_of_mem_nhds hs
  exact (hC.continuousOn γ.2.1 x hx).continuousAt hs

/-- Helper for Lemma 21.3: convexity keeps every affine subdivision point inside the interval. -/
lemma lineMap_mem_of_convex
    (hI : Convex ℝ I) {s t : I} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (s : ℝ) (t : ℝ) u ∈ I := by
  -- Proof comment: every point on the segment joining two points of a convex interval stays in
  -- the interval.
  exact hI.lineMap_mem s.2 t.2 hu

/-- Helper for Lemma 21.3: on a compact metric space, local Hölder control can be made uniform on
small distances. -/
lemma exists_uniformLocalHolderBound_of_compact
    {X : Type*} {Y : Type*} [MetricSpace X] [PseudoMetricSpace Y] [CompactSpace X] [Nonempty X]
    {γ : Set.Ioc (0 : ℝ≥0) 1} {f : X → Y}
    (hf : LocallyHolderWith γ f) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ x y, dist x y < δ →
      dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ) := by
  classical
  choose ε hε C hC using fun x => hf.exists_holderOnWith_ball x
  let U : X → Set X := fun x => Metric.ball x (ε x / 2)
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    exact Metric.mem_ball_self (half_pos (hε x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  have hcover' : (Set.univ : Set X) ⊆ ⋃ i : {x // x ∈ t}, U i.1 := by
    intro x hx
    rcases Set.mem_iUnion.1 (ht hx) with ⟨i, hxi⟩
    rcases Set.mem_iUnion.1 hxi with ⟨hi, hxU⟩
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxU⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun _ => Metric.isOpen_ball) hcover'
  let C₀ : ℝ≥0 := t.sup C
  refine ⟨δ, hδpos, C₀, ?_⟩
  intro x y hxy
  -- Proof comment: the Lebesgue radius places both points in one of the finitely many witness
  -- balls, and the finite supremum of their Hölder constants gives a uniform bound.
  have hxδ : x ∈ Metric.ball x δ := Metric.mem_ball_self hδpos
  rcases hδ x (by simp) with ⟨i, hi⟩
  have hxU : x ∈ U i.1 := hi hxδ
  have hyU : y ∈ U i.1 := hi <| by
    simpa [dist_comm] using Metric.mem_ball.2 hxy
  have hhalf_le : ε i.1 / 2 ≤ ε i.1 := by
    nlinarith [hε i.1]
  have hxBall : x ∈ Metric.ball i.1 (ε i.1) := by
    exact Metric.mem_ball.2 <| (Metric.mem_ball.1 hxU).trans_le hhalf_le
  have hyBall : y ∈ Metric.ball i.1 (ε i.1) := by
    exact Metric.mem_ball.2 <| (Metric.mem_ball.1 hyU).trans_le hhalf_le
  have hlocal : dist (f x) (f y) ≤ C i.1 * dist x y ^ (γ : ℝ) := by
    have hlocal' :
        ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal (C i.1 * dist x y ^ (γ : ℝ)) := by
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using
        hC i.1 x hxBall y hyBall
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlocal'
  have hCi : C i.1 ≤ C₀ := Finset.le_sup i.2
  calc
    dist (f x) (f y) ≤ C i.1 * dist x y ^ (γ : ℝ) := hlocal
    _ ≤ C₀ * dist x y ^ (γ : ℝ) := by gcongr

/-- Helper for Lemma 21.3: consecutive affine subdivision points on a segment are separated by
`dist s t / n`. -/
lemma subdivisionStepDist
    {s t : ℝ} {n k : ℕ} (hn : 0 < n) :
    dist (AffineMap.lineMap s t ((k : ℝ) / n))
      (AffineMap.lineMap s t (((k + 1 : ℕ) : ℝ) / n)) = dist s t / n := by
  -- Proof comment: `dist_lineMap_lineMap` reduces the geometric step size to the scalar gap
  -- between consecutive coefficients, and that gap is exactly `1 / n`.
  rw [dist_lineMap_lineMap]
  have hsub : (((k + 1 : ℕ) : ℝ) - (k : ℝ)) = 1 := by
    norm_num [Nat.cast_add]
  have hcoeff_eq : (((k + 1 : ℕ) : ℝ) / n) - (k : ℝ) / n = 1 / n := by
    calc
      (((k + 1 : ℕ) : ℝ) / n) - (k : ℝ) / n = ((((k + 1 : ℕ) : ℝ) - (k : ℝ)) / n) := by ring
      _ = 1 / n := by rw [hsub]
  have hcoeff : dist (((k + 1 : ℕ) : ℝ) / n) ((k : ℝ) / n) = 1 / n := by
    rw [Real.dist_eq, abs_of_nonneg]
    · simpa [one_div] using hcoeff_eq
    · rw [hcoeff_eq]
      positivity
  rw [dist_comm, hcoeff]
  ring

-- Proof sketch: choose finitely many local Hölder neighborhoods from compactness, take a Lebesgue
-- number for this finite cover, and bound large distances by the sup norm on the compact domain.
/-- Second assertion of Lemma 21.3: if `I` is compact and `f : I → ℝ` is locally Hölder-continuous
of order
`γ ∈ (0,1]`, then `f` is globally Hölder-continuous on `I`. -/
theorem exists_holderWith_of_isCompact
    (hI : IsCompact I)
    (hf : LocallyHolderWith γ f) :
    ∃ C : ℝ≥0, HolderWith C γ f := by
  classical
  by_cases h_nonempty : Nonempty I
  · letI := h_nonempty
    haveI : CompactSpace I := isCompact_iff_compactSpace.mp hI
    have hcont : Continuous f := continuous_of_locallyHolderWith hf
    obtain ⟨δ, hδpos, Cnear, hnear⟩ := exists_uniformLocalHolderBound_of_compact hf
    let D : ℝ := Metric.diam (Set.range f)
    have hDnonneg : 0 ≤ D := Metric.diam_nonneg
    have hdiam : ∀ x y : I, dist (f x) (f y) ≤ D := by
      intro x y
      exact Metric.dist_le_diam_of_mem (isCompact_range hcont).isBounded ⟨x, rfl⟩ ⟨y, rfl⟩
    let Cfar : ℝ≥0 := ⟨D / δ ^ (γ : ℝ), by positivity⟩
    refine ⟨max Cnear Cfar, ?_⟩
    intro x y
    -- Proof comment: for nearby points we use the uniform compactness estimate; for points at
    -- least `δ` apart, the oscillation is bounded by the diameter of the compact image.
    by_cases hxy : dist x y < δ
    · have hlocal : dist (f x) (f y) ≤ max Cnear Cfar * dist x y ^ (γ : ℝ) := by
        exact (hnear x y hxy).trans <| by gcongr; exact le_max_left _ _
      have hlocal' :
          ENNReal.ofReal (dist (f x) (f y)) ≤
            ENNReal.ofReal (max Cnear Cfar * dist x y ^ (γ : ℝ)) :=
        ENNReal.ofReal_le_ofReal hlocal
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using hlocal'
    · have hδle : δ ≤ dist x y := le_of_not_gt hxy
      have hδpow_pos : 0 < δ ^ (γ : ℝ) := by
        positivity
      have hpow : δ ^ (γ : ℝ) ≤ dist x y ^ (γ : ℝ) := by
        gcongr
      have hfar : dist (f x) (f y) ≤ max Cnear Cfar * dist x y ^ (γ : ℝ) := by
        calc
          dist (f x) (f y) ≤ D := hdiam x y
          _ = (D / δ ^ (γ : ℝ)) * δ ^ (γ : ℝ) := by
            field_simp [hδpow_pos.ne']
          _ ≤ (D / δ ^ (γ : ℝ)) * dist x y ^ (γ : ℝ) := by
            gcongr
          _ = Cfar * dist x y ^ (γ : ℝ) := by
            simp [Cfar]
          _ ≤ max Cnear Cfar * dist x y ^ (γ : ℝ) := by
            gcongr
            exact le_max_right _ _
      have hfar' :
          ENNReal.ofReal (dist (f x) (f y)) ≤
            ENNReal.ofReal (max Cnear Cfar * dist x y ^ (γ : ℝ)) :=
        ENNReal.ofReal_le_ofReal hfar
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using hfar'
  · letI : IsEmpty I := ⟨fun x => h_nonempty ⟨x⟩⟩
    exact ⟨0, HolderWith.of_isEmpty⟩

-- Proof sketch: subdivide the segment between two points of the interval into
-- `⌈T / ε⌉` subsegments of length at most `ε`, apply the local small-scale Hölder estimate on
-- each subsegment, and sum the resulting bounds.
/-- Lemma 21.3 (3): for an interval `I` of length at most `T`, a small-scale Hölder estimate with
range `ε` upgrades to a global `γ`-Hölder estimate with constant
`Cε * ⌈T / ε⌉ ^ (1 - γ)`. -/
theorem holderWith_of_small_scale_on_interval
    (hI : Convex ℝ I)
    (hT : ∀ s t : I, dist s t ≤ T)
    (hε : 0 < ε)
    (hsmall :
      ∀ s t : I, dist s t ≤ ε → dist (f t) (f s) ≤ Cε * dist s t ^ (γ : ℝ)) :
    HolderWith (Cε * (Nat.ceil (T / ε) : ℝ≥0) ^ (1 - (γ : ℝ≥0) : ℝ)) γ f := by
  let n : ℕ := Nat.ceil (T / ε)
  by_cases hn0 : n = 0
  · intro s t
    -- Proof comment: `n = 0` forces `T ≤ 0`, so the interval has zero diameter and every pair of
    -- subtype points coincides.
    have hTnonpos : T ≤ 0 := by
      have hdiv_nonpos : T / ε ≤ 0 := Nat.ceil_eq_zero.mp hn0
      rcases (div_nonpos_iff.1 hdiv_nonpos) with h | h
      · linarith
      · exact h.1
    have hdist_zero : dist s t = 0 := le_antisymm ((hT s t).trans hTnonpos) dist_nonneg
    have hst : s = t := dist_eq_zero.1 hdist_zero
    simp [hst]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    intro s t
    have hcoeff_mem : ∀ k : ℕ, min ((k : ℝ) / n) 1 ∈ Set.Icc (0 : ℝ) 1 := by
      intro k
      constructor
      · positivity
      · exact min_le_right _ _
    have hsubdiv_mem :
        ∀ k : ℕ, AffineMap.lineMap (s : ℝ) (t : ℝ) (min ((k : ℝ) / n) 1) ∈ I := by
      intro k
      exact lineMap_mem_of_convex hI (hcoeff_mem k)
    let u : ℕ → I := fun k =>
      ⟨AffineMap.lineMap (s : ℝ) (t : ℝ) (min ((k : ℝ) / n) 1), hsubdiv_mem k⟩
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    have hcoeff_le_one : ∀ {k : ℕ}, k ≤ n → (k : ℝ) / n ≤ 1 := by
      intro k hk
      have hkR : (k : ℝ) ≤ n := by
        exact_mod_cast hk
      exact (div_le_iff₀ hnR).2 <| by simpa [one_mul] using hkR
    have hu_zero : u 0 = s := by
      ext
      simp [u]
    have hu_last : u n = t := by
      ext
      simp [u, Nat.cast_ne_zero.mpr hn.ne']
    have hstep_eq : ∀ {k : ℕ}, k < n → dist (u k) (u (k + 1)) = dist s t / n := by
      intro k hk
      -- Proof comment: for indices below `n`, the capped coefficients are genuine consecutive
      -- fractions `k / n` and `(k + 1) / n`, so the subdivision step size is uniform.
      have hk_le_one : (k : ℝ) / n ≤ 1 := hcoeff_le_one (Nat.le_of_lt hk)
      have hk_succ_le_one : (((k : ℝ) + 1) / n) ≤ 1 := by
        simpa [Nat.cast_add, Nat.cast_one] using hcoeff_le_one (Nat.succ_le_of_lt hk)
      have hk_eq : min ((k : ℝ) / n) 1 = (k : ℝ) / n := min_eq_left hk_le_one
      have hk_succ_eq : min (((k : ℝ) + 1) / n) 1 = ((k : ℝ) + 1) / n := min_eq_left hk_succ_le_one
      have hdist_subdiv :
          dist (u k) (u (k + 1))
            = dist (AffineMap.lineMap (s : ℝ) (t : ℝ) ((k : ℝ) / n))
                (AffineMap.lineMap (s : ℝ) (t : ℝ) (((k + 1 : ℕ) : ℝ) / n)) := by
          simp only [u, Subtype.dist_eq, hk_eq, hk_succ_eq, Nat.cast_add, Nat.cast_one]
      rw [hdist_subdiv]
      exact subdivisionStepDist (s := (s : ℝ)) (t := (t : ℝ)) (n := n) (k := k) hn
    have hstep_le_global : dist s t / n ≤ ε := by
      have hceil : T / ε ≤ n := by
        exact_mod_cast Nat.le_ceil (T / ε)
      have hTdiv : T / n ≤ ε := by
        have hmul : T ≤ (n : ℝ) * ε := (div_le_iff₀ hε).1 hceil
        exact (div_le_iff₀ hnR).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      have hdist_div : dist s t / n ≤ T / n := by
        gcongr
        exact hT s t
      exact hdist_div.trans hTdiv
    have hstep_le : ∀ {k : ℕ}, k < n → dist (u k) (u (k + 1)) ≤ ε := by
      intro k hk
      simpa [hstep_eq hk] using hstep_le_global
    have hchain :
        dist (f (u 0)) (f (u n)) ≤
          ∑ i ∈ Finset.range n, (Cε : ℝ) * (dist s t / n) ^ (γ : ℝ) := by
      -- Proof comment: sum the identical small-scale Hölder estimates along the affine
      -- subdivision chain.
      refine dist_le_range_sum_of_dist_le (f := fun k ↦ f (u k)) n ?_
      intro k hk
      simpa [dist_comm, hstep_eq hk] using hsmall (u k) (u (k + 1)) (hstep_le hk)
    have hsum :
        ∑ i ∈ Finset.range n, (Cε : ℝ) * (dist s t / n) ^ (γ : ℝ) =
          ((Cε * (n : ℝ≥0) ^ (1 - (γ : ℝ≥0) : ℝ)) : ℝ) * dist s t ^ (γ : ℝ) := by
      -- Proof comment: every summand is the same, and the resulting scalar factor is exactly
      -- `n^(1 - γ)` after rewriting the power of `dist s t / n`.
      calc
        ∑ i ∈ Finset.range n, (Cε : ℝ) * (dist s t / n) ^ (γ : ℝ)
            = (n : ℝ) * ((Cε : ℝ) * (dist s t / n) ^ (γ : ℝ)) := by
              simp
        _ = (Cε : ℝ) * ((n : ℝ) * (dist s t / n) ^ (γ : ℝ)) := by
              ring
        _ = (Cε : ℝ) * ((n : ℝ) ^ (1 - (γ : ℝ)) * dist s t ^ (γ : ℝ)) := by
              congr 1
              calc
                (n : ℝ) * (dist s t / n) ^ (γ : ℝ)
                    = (n : ℝ) * (dist s t ^ (γ : ℝ) / (n : ℝ) ^ (γ : ℝ)) := by
                        rw [Real.div_rpow dist_nonneg hnR.le]
                _ = ((n : ℝ) / (n : ℝ) ^ (γ : ℝ)) * dist s t ^ (γ : ℝ) := by
                      ring
                _ = (n : ℝ) ^ (1 - (γ : ℝ)) * dist s t ^ (γ : ℝ) := by
                      rw [Real.rpow_sub hnR 1 (γ : ℝ), Real.rpow_one]
        _ = ((Cε * (n : ℝ≥0) ^ (1 - (γ : ℝ≥0) : ℝ)) : ℝ) * dist s t ^ (γ : ℝ) := by
              simp [mul_left_comm, mul_comm]
    have hreal :
        dist (f s) (f t) ≤
          ((Cε * (n : ℝ≥0) ^ (1 - (γ : ℝ≥0) : ℝ)) : ℝ) * dist s t ^ (γ : ℝ) := by
      calc
        dist (f s) (f t) = dist (f (u 0)) (f (u n)) := by
          simp [hu_zero, hu_last]
        _ ≤ ∑ i ∈ Finset.range n, (Cε : ℝ) * (dist s t / n) ^ (γ : ℝ) := hchain
        _ = ((Cε * (n : ℝ≥0) ^ (1 - (γ : ℝ≥0) : ℝ)) : ℝ) * dist s t ^ (γ : ℝ) := hsum
    -- Route correction: keep the subdivision constant as one bundled `NNReal` term and cast it
    -- once, instead of reopening factor-level `ENNReal` powers of `n`.
    let c : ℝ≥0 := Cε * (n : ℝ≥0) ^ (1 - (γ : ℝ≥0) : ℝ)
    let A : ENNReal := c
    have hc_nonneg : 0 ≤ (c : ℝ) := by
      positivity
    have hcENN : ENNReal.ofReal (c : ℝ) = A := by
      simpa [A, c] using (ENNReal.ofReal_coe_nnreal (p := c))
    have hdistPow :
        ENNReal.ofReal (dist s t ^ (γ : ℝ)) = ENNReal.ofReal (dist s t) ^ (γ : ℝ) := by
      exact (ENNReal.ofReal_rpow_of_nonneg dist_nonneg γ.2.1.le).symm
    have hENN :
        edist (f s) (f t) ≤ A * edist s t ^ (γ : ℝ) := by
      rw [edist_dist, edist_dist]
      -- Proof comment: map the real estimate into `ENNReal`, split the product once, cast the
      -- bundled constant directly, and rewrite the distance power to the `edist` form.
      calc
        ENNReal.ofReal (dist (f s) (f t))
            ≤ ENNReal.ofReal ((c : ℝ) * dist s t ^ (γ : ℝ)) := by
              simpa [c] using ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (dist s t ^ (γ : ℝ)) := by
              rw [ENNReal.ofReal_mul hc_nonneg]
        _ = A * ENNReal.ofReal (dist s t ^ (γ : ℝ)) := by
              rw [hcENN]
        _ = A * ENNReal.ofReal (dist s t) ^ (γ : ℝ) := by
              rw [hdistPow]
    simpa [n, A, c] using hENN

end RealLocalHolder
