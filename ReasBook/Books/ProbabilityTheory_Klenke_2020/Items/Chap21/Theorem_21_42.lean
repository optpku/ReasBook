/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

universe u v

local instance theorem2142BrownianPathSpaceMeasurableSpace :
    MeasurableSpace BrownianPathSpace := borel _

local instance theorem2142BrownianPathSpaceBorelSpace : BorelSpace BrownianPathSpace := ⟨rfl⟩

/-- Helper for Theorem 21.42: a finite-interval Kolmogorov bound for a path-valued process
transfers to the canonical coordinate process under its path law. -/
lemma isKolmogorovProcessOnIcc_canonicalProcess_pathLaw
    {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) {X : Ω → BrownianPathSpace}
    (hX : Measurable X) {T α β C : NNReal}
    (hKol :
      IsKolmogorovProcessOnIcc
        (P : Measure Ω) (fun t ω ↦ X ω t) T α β C) :
    IsKolmogorovProcessOnIcc
      ((P.map hX.aemeasurable : ProbabilityMeasure BrownianPathSpace) :
        Measure BrownianPathSpace)
      (fun t ω ↦ ω t) T α β C := by
  rcases hKol with ⟨hα, hβ, hKolCore⟩
  refine ⟨hα, hβ, ?_⟩
  refine
    { measurablePair := ?_
      kolmogorovCondition := ?_
      p_pos := hKolCore.p_pos
      q_pos := hKolCore.q_pos }
  · intro s t
    -- Proof comment: both coordinates are continuous evaluation maps on path space.
    borelize (ℝ × ℝ)
    simpa using
      (Continuous.prodMk (continuous_eval_const s.1) (continuous_eval_const t.1)).measurable
  · intro s t
    -- Proof comment: rewrite the pushforward lower integral along the path map `X`, then apply
    -- the original Kolmogorov estimate on the source space.
    have hIntegrandAEMeas :
        AEMeasurable
          (fun ω : BrownianPathSpace ↦ edist (ω s.1) (ω t.1) ^ (α : ℝ))
          ((P.map hX.aemeasurable : ProbabilityMeasure BrownianPathSpace) :
            Measure BrownianPathSpace) := by
      change AEMeasurable
        (fun ω : BrownianPathSpace ↦ edist (ω s.1) (ω t.1) ^ (α : ℝ))
        ((P.map hX.aemeasurable : ProbabilityMeasure BrownianPathSpace) : Measure BrownianPathSpace)
      fun_prop
    have hMap :
        ∫⁻ ω, edist (ω s.1) (ω t.1) ^ (α : ℝ)
            ∂((P.map hX.aemeasurable : ProbabilityMeasure BrownianPathSpace) :
              Measure BrownianPathSpace) =
          ∫⁻ ω, edist (X ω s.1) (X ω t.1) ^ (α : ℝ) ∂(P : Measure Ω) := by
      simpa using
        (MeasureTheory.lintegral_map'
          (μ := (P : Measure Ω))
          (g := X)
          (f := fun ω : BrownianPathSpace ↦ edist (ω s.1) (ω t.1) ^ (α : ℝ))
          hIntegrandAEMeas
          hX.aemeasurable)
    rw [hMap]
    simpa using hKolCore.kolmogorovCondition s t

/-- Helper for Theorem 21.42: the dyadic bad-tail event from row `m` onward for the canonical
coordinate process on path space. -/
def dyadicBadTail (N : ℕ) (q : NNReal) (m : ℕ) : Set BrownianPathSpace :=
  Set.iUnion fun n : ℕ ↦
    dyadicRowBadEvent (X := fun s (path : BrownianPathSpace) ↦ path s) N q (m + n)

/-- Helper for Theorem 21.42: shifting the dyadic bad-tail start farther out only shrinks the
event. -/
lemma dyadicBadTail_mono {N : ℕ} {q : NNReal} {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    dyadicBadTail N q m₂ ⊆ dyadicBadTail N q m₁ := by
  intro ω hω
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  rcases mem_iUnion.1 hω with ⟨n, hn⟩
  -- Proof comment: a bad row starting at `m₁ + k` is also part of the tail starting at `m₁`.
  exact mem_iUnion.2 ⟨k + n, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn⟩

/-- Helper for Theorem 21.42: once every dyadic row from `m` onward is good for the canonical path
`ω`, the shifted clipped approximants satisfy a geometric step estimate. -/
lemma clippedDyadicApprox_eval_step_le_geometric_of_rowsGoodFrom
    {T q : NNReal} {ω : BrownianPathSpace} {m : ℕ} {t : NNReal}
    (hrows :
      ∀ k ≥ m, ω ∉ dyadicRowBadEvent (X := fun s (path : BrownianPathSpace) ↦ path s) T q k)
    (ht : t ∈ Set.Icc (0 : NNReal) T) :
    ∀ k : ℕ,
      dist (ω (clippedDyadicApprox T t (k + m))) (ω (clippedDyadicApprox T t (k + m + 1))) ≤
        ((2 : ℝ) ^ (-(q : ℝ))) ^ (m + 1) * ((2 : ℝ) ^ (-(q : ℝ))) ^ k := by
  intro k
  have hgood :
      ω ∉ dyadicRowBadEvent (X := fun s (path : BrownianPathSpace) ↦ path s) T q (k + m + 1) := by
    exact hrows (k + m + 1) (by omega)
  have hstep :=
    clippedDyadicApprox_step_le_of_rowGood
      (X := fun s (path : BrownianPathSpace) ↦ path s)
      (T := T)
      (q := q)
      (t := t)
      (n := k + m)
      (ω := ω)
      ht.2
      hgood
  have hpow :
      dyadicStepThreshold q (k + m + 1) =
        ((2 : ℝ) ^ (-(q : ℝ))) ^ (m + 1) * ((2 : ℝ) ^ (-(q : ℝ))) ^ k := by
    rw [dyadicStepThreshold_eq_geomRatio_pow]
    have hadd : k + m + 1 = (m + 1) + k := by
      omega
    rw [hadd, pow_add]
  -- Proof comment: the canonical-path step bound is just the row-good estimate rewritten into
  -- the shifted geometric normal form used by the tail lemma.
  rw [hpow] at hstep
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, dist_comm] using hstep

/-- Helper for Theorem 21.42: if every dyadic row from level `m` onward is good for one
canonical path `ω`, then the row-`n` clipped dyadic approximant stays within the corresponding
geometric tail of the path value `ω t`. -/
lemma dist_clippedDyadicApprox_eval_le_geometricTail_of_rowsGoodFrom
    {T q : NNReal} {ω : BrownianPathSpace} {m n : ℕ} {t : NNReal}
    (hq0 : 0 < q)
    (hrows :
      ∀ k ≥ m, ω ∉ dyadicRowBadEvent (X := fun s (path : BrownianPathSpace) ↦ path s) T q k)
    (ht : t ∈ Set.Icc (0 : NNReal) T)
    (hmn : m ≤ n) :
    dist (ω (clippedDyadicApprox T t n)) (ω t) ≤
      ((2 : ℝ) ^ (-(q : ℝ))) ^ (n + 1) / (1 - (2 : ℝ) ^ (-(q : ℝ))) := by
  -- Route correction: work directly with the canonical path `ω` and the shifted clipped
  -- approximant sequence instead of rebuilding the private good-row limit path from Theorem 21.6.
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  have hr : r < 1 := by
    -- Proof comment: the dyadic ratio `2^{-q}` is strictly contractive because `q > 0`.
    have hq_real : 0 < (q : ℝ) := by
      exact_mod_cast hq0
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  let f : ℕ → ℝ := fun k ↦ ω (clippedDyadicApprox T t (k + m))
  have hstep :
      ∀ k : ℕ, dist (f k) (f (k + 1)) ≤ r ^ (m + 1) * r ^ k := by
    -- Proof comment: every successive jump of the shifted sequence is controlled by one good-row
    -- dyadic increment.
    intro k
    simpa [f, r, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      clippedDyadicApprox_eval_step_le_geometric_of_rowsGoodFrom
        (T := T) (q := q) (ω := ω) (m := m) (t := t) hrows ht k
  have hlimShift :
      Filter.Tendsto (fun k : ℕ ↦ clippedDyadicApprox T t (k + m)) Filter.atTop (nhds t) := by
    -- Proof comment: shifting the clipped approximants by `m` preserves their convergence to `t`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Filter.tendsto_add_atTop_iff_nat m).2 (tendsto_clippedDyadicApprox ht.2)
  have hlim :
      Filter.Tendsto f Filter.atTop (nhds (ω t)) := by
    -- Proof comment: evaluate the convergent clipped times through continuity of the canonical
    -- path `ω`.
    exact (ω.continuous.continuousAt.tendsto.comp hlimShift)
  have hshift :
      dist (ω (clippedDyadicApprox T t n)) (ω t) ≤ r ^ (m + 1) * r ^ (n - m) / (1 - r) := by
    -- Proof comment: the standard geometric-tail lemma applies to the shifted sequence at index
    -- `n - m`.
    simpa [f, Nat.sub_add_cancel hmn] using
      dist_le_of_le_geometric_of_tendsto
        (r := r)
        (C := r ^ (m + 1))
        (f := f)
        hr
        hstep
        hlim
        (n - m)
  have hpow :
      r ^ (m + 1) * r ^ (n - m) = r ^ (n + 1) := by
    -- Proof comment: the shifted exponent collapses back to the original dyadic row number.
    rw [← pow_add]
    congr 1
    omega
  calc
    dist (ω (clippedDyadicApprox T t n)) (ω t)
        ≤ r ^ (m + 1) * r ^ (n - m) / (1 - r) := hshift
    _ = r ^ (n + 1) / (1 - r) := by rw [hpow]
    _ = ((2 : ℝ) ^ (-(q : ℝ))) ^ (n + 1) / (1 - (2 : ℝ) ^ (-(q : ℝ))) := by
          rfl

/-- Helper for Theorem 21.42: if every dyadic row from level `m` onward is good for a canonical
path `ω`, then the oscillation of `ω` on `[0,N]` at the matching dyadic mesh is bounded by the
explicit geometric dyadic tail estimate. -/
lemma compactIntervalOscillation_le_of_rowsGoodFrom
    {N : ℕ} {q : NNReal} {ω : BrownianPathSpace} {m : ℕ}
    (hq0 : 0 < q)
    (hrows :
      ∀ n ≥ m, ω ∉ dyadicRowBadEvent (X := fun s (path : BrownianPathSpace) ↦ path s) N q n) :
    compactIntervalOscillation N ω (((1 / 2 : NNReal) ^ m)) ≤
      Real.toNNReal
        (((1 + (2 : ℝ) ^ (-(q : ℝ))) / (1 - (2 : ℝ) ^ (-(q : ℝ)))) *
          ((2 : ℝ) ^ (-(q : ℝ))) ^ m) := by
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    -- Proof comment: positivity of `q` again makes the dyadic ratio strictly contractive.
    have hq_real : 0 < (q : ℝ) := by
      exact_mod_cast hq0
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  have hden_pos : 0 < 1 - r := by
    linarith
  have hbound_nonneg : 0 ≤ ((1 + r) / (1 - r)) * r ^ m := by
    positivity
  refine
    compactIntervalOscillation_le_of_forall
      N
      ω
      (((1 / 2 : NNReal) ^ m))
      (Real.toNNReal (((1 + r) / (1 - r)) * r ^ m))
      ?_
  intro s t hclose
  by_cases hst : (s : NNReal) ≤ t
  · have hclose' : dist (s : NNReal) t ≤ (1 : ℝ) / (2 : ℝ) ^ m := by
      simpa [dyadicMesh_eq_halfPow m] using hclose
    have hs_tail :
        dist (ω (clippedDyadicApprox N s m)) (ω s) ≤ r ^ (m + 1) / (1 - r) := by
      -- Proof comment: each endpoint is close to its row-`m` clipped approximant by the same
      -- geometric tail bound.
      simpa [r, dist_comm] using
        dist_clippedDyadicApprox_eval_le_geometricTail_of_rowsGoodFrom
          (T := N) (q := q) (ω := ω) (m := m) (n := m) (t := s) hq0 hrows s.2 le_rfl
    have ht_tail :
        dist (ω (clippedDyadicApprox N t m)) (ω t) ≤ r ^ (m + 1) / (1 - r) := by
      simpa [r] using
        dist_clippedDyadicApprox_eval_le_geometricTail_of_rowsGoodFrom
          (T := N) (q := q) (ω := ω) (m := m) (n := m) (t := t) hq0 hrows t.2 le_rfl
    have hrow :
        dist (ω (clippedDyadicApprox N t m)) (ω (clippedDyadicApprox N s m)) ≤ r ^ m := by
      -- Proof comment: on the good row `m`, the two clipped dyadic approximants differ by at
      -- most one threshold jump.
      simpa [r, dyadicStepThreshold_eq_geomRatio_pow, dist_comm] using
        clippedDyadicApprox_pair_le_of_rowGood_of_dist_le
          (X := fun u (path : BrownianPathSpace) ↦ path u)
          (T := N)
          (q := q)
          (s := s)
          (t := t)
          (n := m)
          (ω := ω)
          s.2.2
          t.2.2
          hst
          hclose'
          (hrows m le_rfl)
    have htriangle :
        dist (ω s) (ω t) ≤
          dist (ω s) (ω (clippedDyadicApprox N s m)) +
            dist (ω (clippedDyadicApprox N s m)) (ω (clippedDyadicApprox N t m)) +
            dist (ω (clippedDyadicApprox N t m)) (ω t) := by
      -- Proof comment: insert the two row-`m` clipped approximants between the endpoint values.
      calc
        dist (ω s) (ω t)
            ≤ dist (ω s) (ω (clippedDyadicApprox N s m)) +
                dist (ω (clippedDyadicApprox N s m)) (ω t) := dist_triangle _ _ _
        _ ≤ dist (ω s) (ω (clippedDyadicApprox N s m)) +
              (dist (ω (clippedDyadicApprox N s m)) (ω (clippedDyadicApprox N t m)) +
                dist (ω (clippedDyadicApprox N t m)) (ω t)) := by
              gcongr
              exact dist_triangle _ _ _
        _ = dist (ω s) (ω (clippedDyadicApprox N s m)) +
              dist (ω (clippedDyadicApprox N s m)) (ω (clippedDyadicApprox N t m)) +
              dist (ω (clippedDyadicApprox N t m)) (ω t) := by
              ring
    have hs_tail' :
        dist (ω s) (ω (clippedDyadicApprox N s m)) ≤ r ^ (m + 1) / (1 - r) := by
      simpa [dist_comm] using hs_tail
    have hrow' :
        dist (ω (clippedDyadicApprox N s m)) (ω (clippedDyadicApprox N t m)) ≤ r ^ m := by
      simpa [dist_comm] using hrow
    have hdist :
        dist (ω s) (ω t) ≤ ((1 + r) / (1 - r)) * r ^ m := by
      calc
        dist (ω s) (ω t)
            ≤ dist (ω s) (ω (clippedDyadicApprox N s m)) +
                dist (ω (clippedDyadicApprox N s m)) (ω (clippedDyadicApprox N t m)) +
                dist (ω (clippedDyadicApprox N t m)) (ω t) := htriangle
        _ ≤ r ^ (m + 1) / (1 - r) + r ^ m + r ^ (m + 1) / (1 - r) := by
              gcongr
        _ = ((1 + r) / (1 - r)) * r ^ m := by
              have hden_ne : (1 - r) ≠ 0 := hden_pos.ne'
              rw [pow_succ]
              field_simp [hden_ne]
              ring
    have hnorm :
        ‖ω s - ω t‖ ≤ Real.toNNReal (((1 + r) / (1 - r)) * r ^ m) := by
      rw [Real.toNNReal_of_nonneg hbound_nonneg]
      simpa [dist_eq_norm] using hdist
    exact nnnorm_le_of_norm_le hnorm
  · have hts : (t : NNReal) ≤ s := le_of_not_ge hst
    have hclose' : dist (t : NNReal) s ≤ (1 : ℝ) / (2 : ℝ) ^ m := by
      simpa [dist_comm, dyadicMesh_eq_halfPow m] using hclose
    have ht_tail :
        dist (ω (clippedDyadicApprox N t m)) (ω t) ≤ r ^ (m + 1) / (1 - r) := by
      simpa [r] using
        dist_clippedDyadicApprox_eval_le_geometricTail_of_rowsGoodFrom
          (T := N) (q := q) (ω := ω) (m := m) (n := m) (t := t) hq0 hrows t.2 le_rfl
    have hs_tail :
        dist (ω (clippedDyadicApprox N s m)) (ω s) ≤ r ^ (m + 1) / (1 - r) := by
      simpa [r] using
        dist_clippedDyadicApprox_eval_le_geometricTail_of_rowsGoodFrom
          (T := N) (q := q) (ω := ω) (m := m) (n := m) (t := s) hq0 hrows s.2 le_rfl
    have hrow :
        dist (ω (clippedDyadicApprox N s m)) (ω (clippedDyadicApprox N t m)) ≤ r ^ m := by
      -- Proof comment: after swapping the endpoints, the same good-row row-`m` bound applies.
      simpa [r, dyadicStepThreshold_eq_geomRatio_pow, dist_comm] using
        clippedDyadicApprox_pair_le_of_rowGood_of_dist_le
          (X := fun u (path : BrownianPathSpace) ↦ path u)
          (T := N)
          (q := q)
          (s := t)
          (t := s)
          (n := m)
          (ω := ω)
          t.2.2
          s.2.2
          hts
          hclose'
          (hrows m le_rfl)
    have htriangle :
        dist (ω t) (ω s) ≤
          dist (ω t) (ω (clippedDyadicApprox N t m)) +
            dist (ω (clippedDyadicApprox N t m)) (ω (clippedDyadicApprox N s m)) +
            dist (ω (clippedDyadicApprox N s m)) (ω s) := by
      calc
        dist (ω t) (ω s)
            ≤ dist (ω t) (ω (clippedDyadicApprox N t m)) +
                dist (ω (clippedDyadicApprox N t m)) (ω s) := dist_triangle _ _ _
        _ ≤ dist (ω t) (ω (clippedDyadicApprox N t m)) +
              (dist (ω (clippedDyadicApprox N t m)) (ω (clippedDyadicApprox N s m)) +
                dist (ω (clippedDyadicApprox N s m)) (ω s)) := by
              gcongr
              exact dist_triangle _ _ _
        _ = dist (ω t) (ω (clippedDyadicApprox N t m)) +
              dist (ω (clippedDyadicApprox N t m)) (ω (clippedDyadicApprox N s m)) +
              dist (ω (clippedDyadicApprox N s m)) (ω s) := by
              ring
    have ht_tail' :
        dist (ω t) (ω (clippedDyadicApprox N t m)) ≤ r ^ (m + 1) / (1 - r) := by
      simpa [dist_comm] using ht_tail
    have hrow' :
        dist (ω (clippedDyadicApprox N t m)) (ω (clippedDyadicApprox N s m)) ≤ r ^ m := by
      simpa [dist_comm] using hrow
    have hdist :
        dist (ω t) (ω s) ≤ ((1 + r) / (1 - r)) * r ^ m := by
      calc
        dist (ω t) (ω s)
            ≤ dist (ω t) (ω (clippedDyadicApprox N t m)) +
                dist (ω (clippedDyadicApprox N t m)) (ω (clippedDyadicApprox N s m)) +
                dist (ω (clippedDyadicApprox N s m)) (ω s) := htriangle
        _ ≤ r ^ (m + 1) / (1 - r) + r ^ m + r ^ (m + 1) / (1 - r) := by
              gcongr
        _ = ((1 + r) / (1 - r)) * r ^ m := by
              have hden_ne : (1 - r) ≠ 0 := hden_pos.ne'
              rw [pow_succ]
              field_simp [hden_ne]
              ring
    have hnorm :
        ‖ω t - ω s‖ ≤ Real.toNNReal (((1 + r) / (1 - r)) * r ^ m) := by
      rw [Real.toNNReal_of_nonneg hbound_nonneg]
      simpa [dist_eq_norm, dist_comm] using hdist
    have hnorm' :
        ‖ω s - ω t‖ ≤ Real.toNNReal (((1 + r) / (1 - r)) * r ^ m) := by
      simpa [norm_sub_rev] using hnorm
    exact nnnorm_le_of_norm_le hnorm'

/-- Helper for Theorem 21.42: once the explicit dyadic oscillation bound at level `m` is at most
`η`, any path with larger oscillation must have a bad dyadic row at or above `m`. -/
lemma badOscillation_subset_dyadicBadTail
    {N : ℕ} {q η : NNReal} {m : ℕ}
    (hq0 : 0 < q)
    (hbound :
      Real.toNNReal
          (((1 + (2 : ℝ) ^ (-(q : ℝ))) / (1 - (2 : ℝ) ^ (-(q : ℝ)))) *
            ((2 : ℝ) ^ (-(q : ℝ))) ^ m) ≤
        η) :
    {ω : BrownianPathSpace | η < compactIntervalOscillation N ω (((1 / 2 : NNReal) ^ m))} ⊆
      dyadicBadTail N q m := by
  intro ω hω
  by_contra htail
  have hrows :
      ∀ n ≥ m, ω ∉ dyadicRowBadEvent (X := fun s (path : BrownianPathSpace) ↦ path s) N q n := by
    intro n hn
    rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
    intro hbad
    apply htail
    change ω ∈ dyadicBadTail N q m
    exact mem_iUnion.2 ⟨k, hbad⟩
  have hsmall :
      compactIntervalOscillation N ω (((1 / 2 : NNReal) ^ m)) ≤ η := by
    -- Proof comment: outside the dyadic bad tail, the deterministic good-row oscillation bound
    -- applies at row `m`.
    exact
      (compactIntervalOscillation_le_of_rowsGoodFrom
        (N := N) (q := q) (ω := ω) (m := m) hq0 hrows).trans hbound
  exact (not_lt_of_ge hsmall) hω

/-- Helper for Theorem 21.42: one common Kolmogorov datum `(α, β, C)` yields one common dyadic
tail cutoff for the bad-row events of all path laws in the family. -/
lemma measure_dyadicBadTail_le_of_uniformKolmogorov
    {I : Type v} (μ : I → ProbabilityMeasure BrownianPathSpace)
    {N : ℕ} {α β C q : NNReal}
    (hKol :
      ∀ i,
        IsKolmogorovProcessOnIcc
          (μ i : Measure BrownianPathSpace)
            (fun t (path : BrownianPathSpace) ↦ path t) N α β C)
    (hgap : 0 < (β : ℝ) - (α : ℝ) * q)
    (ε : NNReal) (hε : 0 < ε) :
    ∃ m : ℕ,
      ∀ i, (μ i : Measure BrownianPathSpace) (dyadicBadTail N q m) ≤ (ε : ℝ≥0∞) := by
  let A : ℝ := (Nat.ceil (N : ℝ) : ℝ) * C
  let ρ : ℝ := (2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_one : ρ < 1 := by
    -- Proof comment: the geometric ratio uses the negative exponent `α q - β`.
    dsimp [ρ]
    have hexp_neg : ((α : ℝ) * q - (β : ℝ)) < 0 := by
      linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) hexp_neg
  have hden_pos : 0 < 1 - ρ := by
    linarith
  have hAone_pos : 0 < A + 1 := by
    positivity
  have hε_real : 0 < (ε : ℝ) := by
    exact_mod_cast hε
  obtain ⟨m, hm⟩ :
      ∃ m : ℕ, ρ ^ m < (ε : ℝ) * (1 - ρ) / (A + 1) := by
    refine exists_pow_lt_of_lt_one ?_ hρ_lt_one
    positivity
  refine ⟨m, ?_⟩
  intro i
  let bad : ℕ → Set BrownianPathSpace :=
    fun n ↦ dyadicRowBadEvent (X := fun s (path : BrownianPathSpace) ↦ path s) N q n
  have hrow_meas :
      ∀ n : ℕ,
        ((μ i : Measure BrownianPathSpace) (bad n)) ≤
          ENNReal.ofReal (A * ρ ^ n) := by
    intro n
    have hrow_real :
        ((μ i : Measure BrownianPathSpace).real (bad n)) ≤ A * ρ ^ n := by
      simpa [A, ρ] using
        measureReal_dyadicRowBadEvent_le_geometric
          (μ := (μ i : Measure BrownianPathSpace))
          (X := fun t (path : BrownianPathSpace) ↦ path t)
          (T := N)
          (α := α)
          (β := β)
          (C := C)
          (q := q)
          (hKol i)
          hgap
          n
    refine
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity : 0 ≤ A * ρ ^ n)).2 ?_
    simpa [Measure.real_def] using hrow_real
  have hsumGeom :
      Summable (fun k : ℕ ↦ A * ρ ^ (m + k)) := by
    have hsumGeom' : Summable (fun k : ℕ ↦ (A * ρ ^ m) * ρ ^ k) :=
      (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left (A * ρ ^ m)
    refine hsumGeom'.congr ?_
    intro k
    rw [pow_add]
    ring
  have hseries :
      ∑' k, ENNReal.ofReal (A * ρ ^ (m + k)) =
        ENNReal.ofReal (A * ρ ^ m / (1 - ρ)) := by
    have hseriesReal :
        ∑' k, A * ρ ^ (m + k) = A * ρ ^ m / (1 - ρ) := by
      calc
        ∑' k, A * ρ ^ (m + k) = ∑' k, (A * ρ ^ m) * ρ ^ k := by
          congr with k
          rw [pow_add]
          ring
        _ = (A * ρ ^ m) * ∑' k, ρ ^ k := by
              rw [tsum_mul_left]
        _ = (A * ρ ^ m) * (1 - ρ)⁻¹ := by
              rw [tsum_geometric_of_lt_one hρ_nonneg hρ_lt_one]
        _ = A * ρ ^ m / (1 - ρ) := by
              rw [div_eq_mul_inv]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) hsumGeom]
    exact congrArg ENNReal.ofReal hseriesReal
  have htail_small :
      A * ρ ^ m / (1 - ρ) < ε := by
    have hdiv :
        ρ ^ m / (1 - ρ) < (ε : ℝ) / (A + 1) := by
      refine (div_lt_iff₀ hden_pos).2 ?_
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm
    have hscaled_le :
        A * (ρ ^ m / (1 - ρ)) ≤ A * ((ε : ℝ) / (A + 1)) := by
      gcongr
    have hAfrac_lt :
        A * ((ε : ℝ) / (A + 1)) < ε := by
      calc
        A * ((ε : ℝ) / (A + 1)) = (ε : ℝ) * (A / (A + 1)) := by
          field_simp [hAone_pos.ne']
        _ < (ε : ℝ) * 1 := by
              refine mul_lt_mul_of_pos_left ?_ hε_real
              refine (div_lt_iff₀ hAone_pos).2 ?_
              linarith
        _ = ε := by ring
    calc
      A * ρ ^ m / (1 - ρ) = A * (ρ ^ m / (1 - ρ)) := by ring
      _ ≤ A * ((ε : ℝ) / (A + 1)) := hscaled_le
      _ < ε := hAfrac_lt
  calc
    ((μ i : Measure BrownianPathSpace) (dyadicBadTail N q m))
        = ((μ i : Measure BrownianPathSpace) (Set.iUnion fun k : ℕ ↦ bad (m + k))) := by
            rfl
    _ ≤ ∑' k : ℕ, ((μ i : Measure BrownianPathSpace) (bad (m + k))) := by
          exact measure_iUnion_le (fun k ↦ bad (m + k))
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (A * ρ ^ (m + k)) := by
          exact ENNReal.tsum_le_tsum fun k ↦ hrow_meas (m + k)
    _ = ENNReal.ofReal (A * ρ ^ m / (1 - ρ)) := hseries
    _ ≤ (ε : ℝ≥0∞) := by
          simpa using ENNReal.ofReal_le_ofReal htail_small.le

/-- Helper for Theorem 21.42: common finite-interval Kolmogorov data for a family of path laws
should imply the uniform oscillation criterion from Theorem 21.40. -/
lemma uniformlySmallCompactIntervalOscillation_of_uniformKolmogorovCriterion
    {I : Type v} (μ : I → ProbabilityMeasure BrownianPathSpace)
    (η ε : NNReal) (hη : 0 < η) (hε : 0 < ε) (N : ℕ)
    (_hN : 0 < (N : NNReal)) {α β C : NNReal}
    (hKol :
      ∀ i,
            IsKolmogorovProcessOnIcc
              (μ i : Measure BrownianPathSpace) (fun t path ↦ path t) N α β C) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ i, μ i {ω | η < compactIntervalOscillation N ω δ} ≤ ε := by
  by_cases hI : Nonempty I
  · rcases hI with ⟨i0⟩
    have hα : 0 < α := (hKol i0).alpha_pos
    have hβ : 0 < β := (hKol i0).beta_pos
    let q : NNReal := β / (2 * α)
    have hq0 : 0 < q := by
      dsimp [q]
      positivity
    have hgap : 0 < (β : ℝ) - (α : ℝ) * q := by
      -- Proof comment: the symmetric choice `q = β / (2 α)` leaves a strictly positive gap in
      -- the geometric row-probability exponent.
      have hα_real : 0 < (α : ℝ) := by
        exact_mod_cast hα
      have hβ_real : 0 < (β : ℝ) := by
        exact_mod_cast hβ
      have htwoα_pos : 0 < ((2 : ℝ) * α) := by
        positivity
      have hq_eq : (q : ℝ) = (β : ℝ) / ((2 : ℝ) * α) := by
        simp [q, NNReal.coe_div, NNReal.coe_mul]
      rw [hq_eq]
      field_simp [htwoα_pos.ne']
      nlinarith
    let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
    let L : ℝ := (1 + r) / (1 - r)
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      positivity
    have hr_lt_one : r < 1 := by
      have hq_real : 0 < (q : ℝ) := by
        exact_mod_cast hq0
      dsimp [r]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
    have hL_pos : 0 < L := by
      dsimp [L]
      refine div_pos ?_ ?_
      · linarith
      · linarith
    have hL_nonneg : 0 ≤ L := hL_pos.le
    have hLone_pos : 0 < L + 1 := by
      linarith
    obtain ⟨mOsc, hmOsc⟩ :
        ∃ m : ℕ, r ^ m < (η : ℝ) / (L + 1) := by
      refine exists_pow_lt_of_lt_one ?_ hr_lt_one
      positivity
    have hOscSmallBase : L * r ^ mOsc < η := by
      have hmul :
          L * r ^ mOsc < L * ((η : ℝ) / (L + 1)) := by
        exact mul_lt_mul_of_pos_left hmOsc hL_pos
      have hfrac_le :
          L * ((η : ℝ) / (L + 1)) ≤ η := by
        calc
          L * ((η : ℝ) / (L + 1)) = (η : ℝ) * (L / (L + 1)) := by
            field_simp [hLone_pos.ne']
          _ ≤ (η : ℝ) * 1 := by
                gcongr
                refine (div_le_iff₀ hLone_pos).2 ?_
                linarith
          _ = η := by ring
      exact lt_of_lt_of_le hmul hfrac_le
    obtain ⟨mTail, hmTail⟩ :=
      measure_dyadicBadTail_le_of_uniformKolmogorov μ hKol hgap ε hε
    let m : ℕ := max mOsc mTail
    let δ : NNReal := ((1 / 2 : NNReal) ^ m)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hOscBound :
        Real.toNNReal
            (((1 + (2 : ℝ) ^ (-(q : ℝ))) / (1 - (2 : ℝ) ^ (-(q : ℝ)))) *
              ((2 : ℝ) ^ (-(q : ℝ))) ^ m) ≤
          η := by
      have hpow_mono : r ^ m ≤ r ^ mOsc := by
        exact pow_le_pow_of_le_one hr_nonneg (le_of_lt hr_lt_one) (le_max_left mOsc mTail)
      have hOscBoundReal :
          L * r ^ m ≤ η := by
        exact le_trans (mul_le_mul_of_nonneg_left hpow_mono hL_nonneg) hOscSmallBase.le
      apply Real.toNNReal_le_iff_le_coe.2
      simpa [L, r] using hOscBoundReal
    refine ⟨δ, hδ_pos, ?_⟩
    intro i
    let bad : ℕ → Set BrownianPathSpace :=
      fun n ↦ dyadicRowBadEvent (X := fun s path ↦ path s) N q n
    have hBadSubset :
        {ω : BrownianPathSpace | η < compactIntervalOscillation N ω δ} ⊆
          dyadicBadTail N q m := by
      -- Route correction: specialize the dyadic good-row argument directly to the canonical path
      -- `ω` instead of rebuilding the private finite-interval good-row limit path.
      simpa [δ, bad] using
        badOscillation_subset_dyadicBadTail
          (N := N) (q := q) (η := η) (m := m) hq0 hOscBound
    have hTailSubset :
        dyadicBadTail N q m ⊆ dyadicBadTail N q mTail := by
      -- Proof comment: starting the bad tail later can only shrink the event.
      simpa [m] using
        (dyadicBadTail_mono (N := N) (q := q) (m₁ := mTail) (m₂ := max mOsc mTail)
          (le_max_right mOsc mTail))
    have hBadMeasure :
        (μ i : Measure BrownianPathSpace) {ω | η < compactIntervalOscillation N ω δ} ≤
          (ε : ℝ≥0∞) := by
      calc
        (μ i : Measure BrownianPathSpace) {ω | η < compactIntervalOscillation N ω δ}
            ≤ (μ i : Measure BrownianPathSpace) (dyadicBadTail N q m) := by
                exact measure_mono hBadSubset
        _ ≤ (μ i : Measure BrownianPathSpace) (dyadicBadTail N q mTail) := by
              exact measure_mono hTailSubset
        _ ≤ (ε : ℝ≥0∞) := hmTail i
    have hBadMeasure' :
        (((μ i {ω | η < compactIntervalOscillation N ω δ} : NNReal) : ℝ≥0∞) ≤
          (ε : ℝ≥0∞)) := by
      simpa using hBadMeasure
    exact ENNReal.coe_le_coe.mp hBadMeasure'
  · refine ⟨1, by norm_num, ?_⟩
    intro i
    exact (hI ⟨i⟩).elim

-- Proof sketch: use the Kolmogorov--Chentsov Hölder-probability estimate on each compact time
-- interval to verify the oscillation tightness criterion from Theorem 21.40 for the family of
-- path laws, then apply that criterion together with the assumed tightness of the initial-value
-- laws.
/-- Theorem 21.42: tight initial laws together with Kolmogorov moment bounds on every bounded time
interval imply weak relative compactness of the family of path laws in `C([0, ∞), ℝ)`. -/
theorem isCompact_closure_range_pathLaw_of_tight_initialLaws_of_kolmogorovCriterion
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : I → Ω → BrownianPathSpace)
    (hX : ∀ i, Measurable (X i))
    (h0_tight :
      initial_value_laws_tight (fun i ↦ P.map (hX i).aemeasurable))
    (hmoment :
      ∀ N : NNReal, 0 < N →
        ∃ α β C : NNReal,
          ∀ i,
            IsKolmogorovProcessOnIcc
              (P : Measure Ω) (fun t ω ↦ X i ω t) N α β C) :
    IsCompact (closure (Set.range fun i ↦ P.map (hX i).aemeasurable)) := by
  let μ : I → ProbabilityMeasure BrownianPathSpace := fun i ↦ P.map (hX i).aemeasurable
  have hOsc : uniformly_small_compact_interval_path_oscillation_probabilities μ := by
    intro η ε hη hε N
    by_cases hN : N = 0
    · refine ⟨1, by norm_num, ?_⟩
      intro i
      have hOscZero (ω : BrownianPathSpace) : compactIntervalOscillation 0 ω 1 = 0 := by
        refine le_antisymm ?_ bot_le
        refine compactIntervalOscillation_le_of_forall 0 ω 1 0 ?_
        intro s t _hstep
        have hs0 : (s : NNReal) = 0 := le_antisymm (by simpa using s.2.2) s.2.1
        have ht0 : (t : NNReal) = 0 := le_antisymm (by simpa using t.2.2) t.2.1
        simp [hs0, ht0]
      have hBadEmpty : {ω : BrownianPathSpace | η < compactIntervalOscillation 0 ω 1} = ∅ := by
        ext ω
        simp [hOscZero ω]
      simp [μ, hN, hBadEmpty]
    · have hNpos : 0 < (N : NNReal) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hN
      rcases hmoment N hNpos with ⟨α, β, C, hKol⟩
      have hKolPath :
          ∀ i,
            IsKolmogorovProcessOnIcc
              (μ i : Measure BrownianPathSpace) (fun t ω ↦ ω t) N α β C := by
        intro i
        simpa [μ] using
          isKolmogorovProcessOnIcc_canonicalProcess_pathLaw
            P (hX i) (hKol i)
      exact
        uniformlySmallCompactIntervalOscillation_of_uniformKolmogorovCriterion
          μ η ε hη hε N hNpos hKolPath
  -- Proof comment: Theorem 21.40 converts tight initial laws and the uniform oscillation control
  -- into relative compactness of the family of path laws.
  simpa [μ] using isCompact_closure_path_measure_family_of_controls μ h0_tight hOsc
