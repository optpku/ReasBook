/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

variable {μ ν : ProbabilityMeasure ℝ}

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Theorem 16.27: the canonical embedding `ℝ → EuclideanSpace ℝ (Fin 1)`. -/
private noncomputable def realToEuclideanOne : ℝ → E1 :=
  fun t ↦ EuclideanSpace.single 0 t

/-- Helper for Theorem 16.27: read the unique coordinate of `EuclideanSpace ℝ (Fin 1)`. -/
private def euclideanOneToReal : E1 → ℝ :=
  fun x ↦ x 0

/-- Helper for Theorem 16.27: the canonical embedding `ℝ → EuclideanSpace ℝ (Fin 1)` is
continuous. -/
private lemma continuous_realToEuclideanOne : Continuous realToEuclideanOne := by
  have hsingle : Continuous fun t : ℝ ↦ (Pi.single (0 : Fin 1) t : Fin 1 → ℝ) := by
    refine _root_.continuous_pi ?_
    intro i
    fin_cases i
    simpa using continuous_id
  simpa [realToEuclideanOne, EuclideanSpace.single] using
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 1 ↦ ℝ)).comp hsingle

/-- Helper for Theorem 16.27: the canonical embedding `ℝ → EuclideanSpace ℝ (Fin 1)` preserves
distances. -/
private lemma dist_realToEuclideanOne (x y : ℝ) :
    dist (realToEuclideanOne x) (realToEuclideanOne y) = dist x y := by
  exact
    PiLp.dist_single_same
      (p := (2 : ENNReal)) (β := fun _ : Fin 1 ↦ ℝ) (i := (0 : Fin 1)) x y

/-- Helper for Theorem 16.27: the canonical embedding `ℝ → EuclideanSpace ℝ (Fin 1)` is
a.e.-measurable for every measure. -/
private lemma aemeasurable_realToEuclideanOne (ρ : Measure ℝ) :
    AEMeasurable realToEuclideanOne ρ :=
  continuous_realToEuclideanOne.measurable.aemeasurable

/-- Helper for Theorem 16.27: push a real probability law to `EuclideanSpace ℝ (Fin 1)` along the
canonical embedding. -/
private noncomputable def pushRealToEuclideanOne (ρ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure E1 :=
  ρ.map (aemeasurable_realToEuclideanOne (ρ : Measure ℝ))

/-- Helper for Theorem 16.27: transporting a real probability law along the canonical embedding
preserves the characteristic function after reading the unique coordinate. -/
private lemma charFun_map_realToEuclideanOne (ρ : ProbabilityMeasure ℝ) (x : E1) :
    charFun (pushRealToEuclideanOne ρ : Measure E1) x =
      charFun (ρ : Measure ℝ) (euclideanOneToReal x) := by
  change charFun (Measure.map realToEuclideanOne (ρ : Measure ℝ)) x =
    charFun (ρ : Measure ℝ) (euclideanOneToReal x)
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply_real,
    MeasureTheory.integral_map (aemeasurable_realToEuclideanOne (ρ : Measure ℝ)) (by fun_prop)]
  congr with t
  congr 1
  have hinner :
      inner ℝ (EuclideanSpace.single (0 : Fin 1) t) x = euclideanOneToReal x * t := by
    simpa [euclideanOneToReal, mul_comm] using
      (EuclideanSpace.inner_single_left (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner)

/-- Helper for Theorem 16.27: weak convergence of real probability laws upgrades to compact-uniform
convergence of characteristic functions. -/
private lemma charFunTendstoUniformlyOn_ofTendstoReal
    {ρ : ProbabilityMeasure ℝ} {ρs : ℕ → ProbabilityMeasure ℝ}
    (hρ : Tendsto ρs atTop (𝓝 ρ)) :
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n t ↦ charFun (ρs n) t) (charFun ρ) atTop K := by
  let F : ℕ → ℝ → ℂ := fun n t ↦ charFun (ρs n : Measure ℝ) t
  have h_pointwise : ∀ t : ℝ, Tendsto (fun n ↦ F n t) atTop (𝓝 (charFun ρ t)) := by
    exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hρ
  let Qs : ℕ → ProbabilityMeasure E1 := fun n ↦ pushRealToEuclideanOne (ρs n)
  have h_measures :
      (((↑) : ProbabilityMeasure E1 → Measure E1) '' Set.range Qs) =
        Set.range (fun n ↦ ((Qs n : ProbabilityMeasure E1) : Measure E1)) := by
    ext η
    constructor
    · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Qs n, ⟨n, rfl⟩, rfl⟩
  have h_pointwise_push :
      ∀ x : E1,
        Tendsto (fun n ↦ charFun ((Qs n : ProbabilityMeasure E1) : Measure E1) x) atTop
          (𝓝 (charFun (pushRealToEuclideanOne ρ : Measure E1) x)) := by
    intro x
    simpa [Qs, charFun_map_realToEuclideanOne] using h_pointwise (euclideanOneToReal x)
  have h_tight_range :
      IsTightMeasureSet (Set.range fun n ↦ ((Qs n : ProbabilityMeasure E1) : Measure E1)) := by
    exact isTightMeasureSet_of_tendsto_charFun (by fun_prop) h_pointwise_push
  have h_tight :
      IsTightMeasureSet (((↑) : ProbabilityMeasure E1 → Measure E1) '' Set.range Qs) := by
    rw [h_measures]
    exact h_tight_range
  have h_charFuns_push :
      charFun '' (((↑) : ProbabilityMeasure E1 → Measure E1) '' Set.range Qs) =
        Set.range (fun n x ↦ charFun (Qs n : Measure E1) x) := by
    ext φ
    constructor
    · rintro ⟨η, hη, rfl⟩
      rcases hη with ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(Qs n : Measure E1), ⟨Qs n, ⟨n, rfl⟩, rfl⟩, rfl⟩
  have h_eqcont_push_set :
      (Set.range fun n x ↦ charFun (Qs n : Measure E1) x).UniformEquicontinuous := by
    rw [← h_charFuns_push]
    exact tight_probabilityMeasureFamily_charFunSet_uniformEquicontinuous (Set.range Qs) h_tight
  have h_eqcont_push_range :
      UniformEquicontinuous ((↑) : Set.range (fun n x ↦ charFun (Qs n : Measure E1) x) → E1 → ℂ) :=
    h_eqcont_push_set
  have h_eqcont_push : UniformEquicontinuous (fun n x ↦ charFun (Qs n : Measure E1) x) :=
    uniformEquicontinuous_iff_range.2 h_eqcont_push_range
  have h_eqcont : UniformEquicontinuous F := by
    rw [Metric.uniformEquicontinuous_iff] at h_eqcont_push ⊢
    intro ε hε
    rcases h_eqcont_push ε hε with ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro x y hxy n
    have hxyE : dist (realToEuclideanOne x) (realToEuclideanOne y) < δ := by
      simpa [dist_realToEuclideanOne] using hxy
    simpa [F, Qs, charFun_map_realToEuclideanOne] using
      hδ (realToEuclideanOne x) (realToEuclideanOne y) hxyE n
  intro K hK
  let FK : ℕ → K → ℝ := fun n x ↦ dist (F n x.1) (charFun (ρ : Measure ℝ) x.1)
  have hFK_pointwise : ∀ x : K, Tendsto (fun n ↦ FK n x) atTop (𝓝 0) := by
    intro x
    have hdist :
        Tendsto
          (fun n ↦ dist (F n x.1) (charFun (ρ : Measure ℝ) x.1))
          atTop
          (𝓝 (dist (charFun (ρ : Measure ℝ) x.1) (charFun (ρ : Measure ℝ) x.1))) := by
      exact (h_pointwise x.1).dist tendsto_const_nhds
    simpa [FK, F] using hdist
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcharFunρ_cont : Continuous fun x : K ↦ charFun (ρ : Measure ℝ) x.1 := by
    simpa using
      (MeasureTheory.continuous_charFun (μ := (ρ : Measure ℝ))).comp continuous_subtype_val
  have hcharFunρ_uc : UniformContinuous fun x : K ↦ charFun (ρ : Measure ℝ) x.1 :=
    CompactSpace.uniformContinuous_of_continuous hcharFunρ_cont
  have hFK_eqcont : UniformEquicontinuous FK := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    rcases (Metric.uniformEquicontinuous_iff.mp h_eqcont) (ε / 2) (by positivity) with
      ⟨δ₁, hδ₁pos, hδ₁⟩
    rcases (Metric.uniformContinuous_iff.mp hcharFunρ_uc) (ε / 2) (by positivity) with
      ⟨δ₂, hδ₂pos, hδ₂⟩
    refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
    intro x y hxy n
    have hFxy : dist (F n x.1) (F n y.1) < ε / 2 :=
      hδ₁ x.1 y.1 (lt_of_lt_of_le hxy (min_le_left _ _)) n
    have hρxy : dist (charFun (ρ : Measure ℝ) x.1) (charFun (ρ : Measure ℝ) y.1) < ε / 2 :=
      hδ₂ (lt_of_lt_of_le hxy (min_le_right _ _))
    calc
      dist (FK n x) (FK n y)
          ≤ dist (F n x.1) (F n y.1) +
              dist (charFun (ρ : Measure ℝ) x.1) (charFun (ρ : Measure ℝ) y.1) := by
              simpa [FK] using
                dist_dist_dist_le (F n x.1) (charFun (ρ : Measure ℝ) x.1)
                  (F n y.1) (charFun (ρ : Measure ℝ) y.1)
      _ < ε := by nlinarith
  have hFK_uniform :
      TendstoUniformlyOn (fun n x ↦ FK n x) (fun _ : K ↦ (0 : ℝ)) atTop (Set.univ : Set K) :=
    tendstoUniformlyOn_of_pointwise_of_uniformEquicontinuous hFK_pointwise hFK_eqcont isCompact_univ
  rw [Metric.tendstoUniformlyOn_iff] at hFK_uniform ⊢
  intro ε hε
  filter_upwards [hFK_uniform ε hε] with n hn x hx
  simpa [FK, F, dist_comm] using hn ⟨x, hx⟩ (by simp)

/-- Helper for Theorem 16.27: if a positive convolution power of a real probability law is a
Dirac mass, then the original law is already a Dirac mass. -/
lemma eq_diracProba_of_pow_eq_diracProba_viaNormOne
    {σ : ProbabilityMeasure ℝ} {n : ℕ+} {x : ℝ}
    (hpow : σ ^ (n : ℕ) = diracProba x) :
    ∃ y : ℝ, σ = diracProba y := by
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ht_antitone : Antitone fun k ↦ |t k| := by
    intro m n hmn
    -- Proof comment: the reciprocal test sequence decreases monotonically to `0`.
    simp only [t]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      (Nat.one_div_le_one_div (α := ℝ) hmn)
  have ht : Tendsto t atTop (𝓝 0) := by
    -- Proof comment: the same reciprocal sequence tends to `0`.
    have hone :
        Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [t] using hone
  have ht_zero : Tendsto (fun k ↦ |t k|) atTop (𝓝 0) := by
    convert ht using 1
    ext k
    have hk : 0 ≤ t k := by
      dsimp [t]
      positivity
    exact abs_of_nonneg hk
  have ht_nonzero : ∀ k, t k ≠ 0 := by
    intro k
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp [t, hk]
  have hφ_unit : ∀ k, ‖charFun (σ : Measure ℝ) (t k)‖ = 1 := by
    intro k
    have hchar :
        charFun ((σ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) (t k) =
          charFun (Measure.dirac x) (t k) := by
      simpa [MeasureTheory.diracProba] using
        congrArg (fun ρ : ProbabilityMeasure ℝ ↦ charFun (ρ : Measure ℝ) (t k)) hpow
    have hnorm : ‖charFun (σ : Measure ℝ) (t k) ^ (n : ℕ)‖ = 1 := by
      simpa [MeasureTheory.ProbabilityMeasure.charFun_pow, MeasureTheory.charFun_dirac] using
        congrArg norm hchar
    have hpow_one : ‖charFun (σ : Measure ℝ) (t k)‖ ^ (n : ℕ) = 1 := by
      simpa [norm_pow] using hnorm
    have hnonneg : 0 ≤ ‖charFun (σ : Measure ℝ) (t k)‖ := norm_nonneg _
    exact (pow_eq_one_iff_of_nonneg hnonneg n.ne_zero).1 hpow_one
  obtain ⟨y, hy⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  refine ⟨y, ?_⟩
  -- Proof comment: upgrade the measure-level Dirac conclusion to the probability-measure owner.
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hy

/-- Helper for Theorem 16.27: every affine scaling witness in `IsStableInBroadSense μ` is in fact
strictly positive, because a zero scale would force a Dirac convolution power. -/
lemma affineScale_pos_of_isStableInBroadSense
    {a d : ℕ+ → ℝ} (hμ : IsStableInBroadSense μ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hpow : ∀ n : ℕ+, μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, 0 < a n := by
  intro n
  rcases hμ with ⟨hμ_nontrivial, _⟩
  by_contra hna
  have hzero : a n = 0 := le_antisymm (not_lt.mp hna) (ha_nonneg n)
  have hdiracPow : μ ^ (n : ℕ) = diracProba (d n) := by
    -- Proof comment: with zero slope the affine image collapses to a Dirac mass.
    rw [hpow n, hzero]
    apply ProbabilityMeasure.toMeasure_injective
    ext s hs
    simp [hs]
  rcases eq_diracProba_of_pow_eq_diracProba_viaNormOne hdiracPow with ⟨x, hx⟩
  exact hμ_nontrivial x hx

/-- Helper for Theorem 16.27: if `μ ^ n` is obtained from `μ` by an affine map
`x ↦ a n * x + d n` with positive scale, then the corresponding normalized convolution law is
exactly `μ`. -/
lemma normalizedConvolutionLaw_eq_self_of_affinePow
    {a d : ℕ+ → ℝ} (ha : ∀ n : ℕ+, 0 < a n)
    (hpow : ∀ n : ℕ+, μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, normalizedConvolutionLaw μ a d n = μ := by
  intro n
  have ha_ne : a n ≠ 0 := ne_of_gt (ha n)
  -- Rewrite the normalized law using the given affine description of `μ ^ n`.
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map (fun x : ℝ ↦ (a n)⁻¹ * x + -(a n)⁻¹ * d n)
      ((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) =
      (μ : Measure ℝ)
  rw [hpow n, ProbabilityMeasure.toMeasure_map]
  -- Compose the normalization with its inverse affine map to recover the identity.
  rw [Measure.map_map (measurable_affineMap (a n)⁻¹ (-(a n)⁻¹ * d n))
    (measurable_affineMap (a n) (d n))]
  have hcomp :
      (fun x : ℝ ↦ (a n)⁻¹ * (a n * x + d n) + -(a n)⁻¹ * d n) = id := by
    funext x
    field_simp [ha_ne]
    simp
  change
    Measure.map (fun x : ℝ ↦ (a n)⁻¹ * (a n * x + d n) + -(a n)⁻¹ * d n) (μ : Measure ℝ) =
      (μ : Measure ℝ)
  rw [hcomp]
  simp

/-- Helper for Theorem 16.27: on `ℝ`, the real inner product is ordinary multiplication. -/
private lemma realInner_eq_mul (x y : ℝ) : inner ℝ x y = x * y := by
  have h :=
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y
  simp [Real.norm_eq_abs] at h
  nlinarith

/-- Helper for Theorem 16.27: the characteristic function of an affine pushforward on `ℝ`
splits into the scaled characteristic function and the translation phase. -/
private lemma charFun_map_affine_eq
    (σ : ProbabilityMeasure ℝ) (a d t : ℝ) :
    charFun ((map σ (measurable_affineMap a d).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) t =
      charFun (σ : Measure ℝ) (a * t) *
        Complex.exp ((((d * t : ℝ) : ℂ) * Complex.I)) := by
  -- Proof comment: factor the affine map into a scaling followed by a translation, then apply the
  -- standard characteristic-function transport lemmas for those two pieces.
  rw [ProbabilityMeasure.toMeasure_map]
  have hcomp :
      Measure.map (fun x : ℝ ↦ a * x + d) (σ : Measure ℝ) =
        Measure.map (fun x : ℝ ↦ x + d) (Measure.map (fun x : ℝ ↦ a * x) (σ : Measure ℝ)) := by
    rw [show (fun x : ℝ ↦ a * x + d) = (fun x : ℝ ↦ x + d) ∘ fun x : ℝ ↦ a * x from rfl,
      ← Measure.map_map]
    all_goals fun_prop
  rw [hcomp, MeasureTheory.charFun_map_add_const]
  simpa [realInner_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (MeasureTheory.charFun_map_mul (μ := (σ : Measure ℝ)) a t)

/-- Helper for Theorem 16.27: taking a positive convolution power of an affine pushforward keeps
the same slope and multiplies the shift by the power index. -/
private lemma map_affine_pow_eq_map_pow_affine
    (σ : ProbabilityMeasure ℝ) (a d : ℝ) (n : ℕ+) :
    (map σ (measurable_affineMap a d).aemeasurable) ^ (n : ℕ) =
      map (σ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * d)).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_charFun ?_
  ext t
  have hsource :
      charFun
          ((map σ (measurable_affineMap a d).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) t =
        charFun (σ : Measure ℝ) (a * t) *
          Complex.exp ((((d * t : ℝ) : ℂ) * Complex.I)) := by
    -- Proof comment: rewrite the affine pushforward once so the convolution power can be read on
    -- the characteristic-function side.
    exact charFun_map_affine_eq (σ := σ) a d t
  have htarget :
      charFun
          ((map (σ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * d)).aemeasurable :
              ProbabilityMeasure ℝ) : Measure ℝ) t =
        charFun (σ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp ((((((n : ℝ) * d) * t : ℝ) : ℂ) * Complex.I)) := by
    -- Proof comment: the target affine image has the same scaled frequency, and its translation
    -- phase is already normalized to the total shift `(n : ℝ) * d`.
    rw [charFun_map_affine_eq]
    congr 1
    simpa using congrArg (fun f : ℝ → ℂ ↦ f (a * t)) (ProbabilityMeasure.charFun_pow σ (n : ℕ))
  -- Proof comment: both characteristic functions reduce to the same product of the powered
  -- scaled characteristic function and the accumulated translation phase.
  calc
    charFun (((map σ (measurable_affineMap a d).aemeasurable) ^ (n : ℕ) :
        ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun
            ((map σ (measurable_affineMap a d).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) t ^
            (n : ℕ) := by
              simpa using
                congrArg (fun f : ℝ → ℂ ↦ f t)
                  (ProbabilityMeasure.charFun_pow
                    (map σ (measurable_affineMap a d).aemeasurable) (n : ℕ))
    _ = (charFun (σ : Measure ℝ) (a * t) *
          Complex.exp ((((d * t : ℝ) : ℂ) * Complex.I))) ^ (n : ℕ) := by
            rw [hsource]
    _ = charFun (σ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp (((((n : ℝ) * (d * t) : ℝ) : ℂ) * Complex.I)) := by
            rw [mul_pow, (Complex.exp_nat_mul ((((d * t : ℝ) : ℂ) * Complex.I)) (n : ℕ)).symm]
            congr 1
            norm_num
            ring
    _ = charFun (σ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp ((((((n : ℝ) * d) * t : ℝ) : ℂ) * Complex.I)) := by
            congr 2
            ring
    _ = charFun
          ((map (σ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * d)).aemeasurable :
              ProbabilityMeasure ℝ) : Measure ℝ) t := by
            rw [htarget]

/-- Helper for Theorem 16.27: weak convergence of real probability laws is preserved by taking a
fixed positive convolution power. -/
lemma tendsto_pow_of_tendsto
    {ρ : ℕ+ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hρ : Tendsto ρ atTop (𝓝 μ)) (k : ℕ+) :
    Tendsto (fun n : ℕ+ ↦ ρ n ^ (k : ℕ)) atTop (𝓝 (μ ^ (k : ℕ))) := by
  -- Proof comment: pass to characteristic functions, take the fixed power pointwise, and then
  -- rewrite both sides back through `ProbabilityMeasure.charFun_pow`.
  have hρNat : Tendsto (fun n : ℕ ↦ ρ (Nat.succPNat n)) atTop (𝓝 μ) := by
    simpa [OrderIso.pnatIsoNat_symm_apply] using hρ.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  have hpowNat :
      Tendsto (fun n : ℕ ↦ ρ (Nat.succPNat n) ^ (k : ℕ)) atTop (𝓝 (μ ^ (k : ℕ))) := by
    refine
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun
        (μ := fun n : ℕ ↦ ρ (Nat.succPNat n) ^ (k : ℕ)) (μ₀ := μ ^ (k : ℕ)) (E := ℝ)).2 ?_
    intro t
    have hchar := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hρNat t
    simpa [ProbabilityMeasure.charFun_pow] using hchar.pow (k : ℕ)
  have hpowPnat := hpowNat.comp OrderIso.pnatIsoNat.tendsto_atTop
  convert hpowPnat using 1
  ext n
  simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Theorem 16.27: the normalization at time `k * n` is obtained from the `k`th
convolution power of the normalization at time `n` by one explicit affine map. -/
lemma normalizedConvolutionLaw_blockFactorization
    {a b : ℕ+ → ℝ} (ha : ∀ n : ℕ+, 0 < a n) (k n : ℕ+) :
    normalizedConvolutionLaw ν a b (k * n) =
      map ((normalizedConvolutionLaw ν a b n) ^ (k : ℕ))
        (measurable_affineMap (a n / a (k * n))
          ((((k : ℝ) * b n) - b (k * n)) / a (k * n))).aemeasurable := by
  have han_ne : a n ≠ 0 := ne_of_gt (ha n)
  have hakn_ne : a (k * n) ≠ 0 := ne_of_gt (ha (k * n))
  have hpow :
      ((normalizedConvolutionLaw ν a b n) ^ (k : ℕ)) =
        map (ν ^ ((k * n : ℕ)))
          (measurable_affineMap (a n)⁻¹ (((k : ℝ) * (-(a n)⁻¹ * b n)))).aemeasurable := by
    -- Proof comment: first transport the `k`th convolution power through the time-`n`
    -- normalization, then collapse the iterated convolution power to time `k * n`.
    calc
      ((normalizedConvolutionLaw ν a b n) ^ (k : ℕ))
          = (map (ν ^ (n : ℕ))
              (measurable_affineMap (a n)⁻¹ (-(a n)⁻¹ * b n)).aemeasurable) ^ (k : ℕ) := by
              rfl
      _ = map ((ν ^ (n : ℕ)) ^ (k : ℕ))
            (measurable_affineMap (a n)⁻¹ (((k : ℝ) * (-(a n)⁻¹ * b n)))).aemeasurable := by
              simpa using
                map_affine_pow_eq_map_pow_affine
                  (σ := ν ^ (n : ℕ)) (a := (a n)⁻¹) (d := -(a n)⁻¹ * b n) k
      _ = map (ν ^ ((n : ℕ) * (k : ℕ)))
            (measurable_affineMap (a n)⁻¹ (((k : ℝ) * (-(a n)⁻¹ * b n)))).aemeasurable := by
              rw [← pow_mul]
      _ = map (ν ^ ((k * n : ℕ)))
            (measurable_affineMap (a n)⁻¹ (((k : ℝ) * (-(a n)⁻¹ * b n)))).aemeasurable := by
              congr 1
              simp [Nat.mul_comm]
  apply ProbabilityMeasure.toMeasure_injective
  -- Proof comment: compose the block normalization with the normalization already present in the
  -- `k`th power of the time-`n` law, and simplify the affine coefficients to the
  -- `(k * n)`-normalization.
  rw [normalizedConvolutionLaw, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map, hpow, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (measurable_affineMap (a n / a (k * n))
      ((((k : ℝ) * b n) - b (k * n)) / a (k * n)))
    (measurable_affineMap (a n)⁻¹ (((k : ℝ) * (-(a n)⁻¹ * b n))))]
  have hcomp :
      ((fun x : ℝ ↦
          (a n / a (k * n)) * x + ((((k : ℝ) * b n) - b (k * n)) / a (k * n))) ∘
        fun x : ℝ ↦ (a n)⁻¹ * x + ((k : ℝ) * (-(a n)⁻¹ * b n))) =
        fun x : ℝ ↦ (a (k * n))⁻¹ * x + -(a (k * n))⁻¹ * b (k * n) := by
    funext x
    dsimp
    field_simp [han_ne, hakn_ne]
    ring
  rw [hcomp]
  rfl

/-- Helper for Theorem 16.27: a non-Dirac law cannot acquire a Dirac convolution power. -/
lemma powNotDiracOfNotDirac
    {σ : ProbabilityMeasure ℝ} (hσ_nontrivial : ∀ x : ℝ, σ ≠ diracProba x) (k : ℕ+) :
    ∀ x : ℝ, σ ^ (k : ℕ) ≠ diracProba x := by
  intro x hx
  -- Proof comment: pull the Dirac identity for the convolution power back to the original law.
  rcases eq_diracProba_of_pow_eq_diracProba_viaNormOne (σ := σ) (n := k) (x := x) hx with ⟨y, hy⟩
  exact hσ_nontrivial y hy

/-- Helper for Theorem 16.27: if an affine image `τ = map σ (x ↦ c * x + d)` has nonzero slope,
then `σ` is recovered by pushing `τ` forward along the inverse affine map. -/
lemma eq_map_inverse_affine_of_eq_map_affine
    {σ τ : ProbabilityMeasure ℝ} {c d : ℝ} (hc : c ≠ 0)
    (h : τ = map σ (measurable_affineMap c d).aemeasurable) :
    σ = map τ (measurable_affineMap c⁻¹ (-(c⁻¹ * d))).aemeasurable := by
  -- Proof comment: rewrite `τ` by the given affine factorization, then compose with the explicit
  -- inverse affine map and simplify the composite to `id`.
  rw [h]
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_affineMap c⁻¹ (-(c⁻¹ * d))) (measurable_affineMap c d)]
  have hcomp :
      ((fun x : ℝ ↦ c⁻¹ * x + -(c⁻¹ * d)) ∘ fun x : ℝ ↦ c * x + d) = id := by
    funext x
    change c⁻¹ * (c * x + d) + -(c⁻¹ * d) = x
    field_simp [hc]
    ring
  rw [hcomp]
  simp

/-- Helper for Theorem 16.27: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
`atTop` limit. -/
private theorem tendstoPnatAtTopIffSuccPNat {β : Type*} [TopologicalSpace β]
    {f : ℕ+ → β} {l : Filter β} :
    Tendsto f atTop l ↔ Tendsto (fun n : ℕ ↦ f (Nat.succPNat n)) atTop l := by
  constructor
  · intro hf
    -- Proof comment: compose the `ℕ+`-indexed limit with the order isomorphism `ℕ ≃o ℕ+`.
    simpa [OrderIso.pnatIsoNat_symm_apply] using hf.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  · intro hf
    -- Proof comment: compose back with `PNat.natPred` to recover the original `ℕ+` indexing.
    have hcomp := hf.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Theorem 16.27: the nat-indexed affine-pushforward weak-continuity argument reduces
to compact-uniform convergence of characteristic functions on one bounded frequency interval. -/
private lemma tendstoMapAffineOfTendstoOfCoefficientsNatCore
    {ηs : ℕ → ProbabilityMeasure ℝ} {η : ProbabilityMeasure ℝ}
    {c d : ℕ → ℝ} {cLim dLim B : ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hc : Tendsto c atTop (𝓝 cLim))
    (hd : Tendsto d atTop (𝓝 dLim))
    (hBound : ∀ n : ℕ, |c n| ≤ B) :
    Tendsto (fun n : ℕ ↦ map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
      atTop (𝓝 (map η (measurable_affineMap cLim dLim).aemeasurable)) := by
  -- Route correction: reuse the earlier Chapter 16 owner theorem for compact-uniform
  -- characteristic-function convergence instead of rebuilding that bridge locally.
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 ?_
  intro t
  let K : Set ℝ := Set.Icc (-(B * |t|)) (B * |t|)
  have hK : IsCompact K := isCompact_Icc
  have huni :
      TendstoUniformlyOn (fun n s ↦ charFun (ηs n : Measure ℝ) s)
        (charFun (η : Measure ℝ)) atTop K :=
    charFunTendstoUniformlyOn_ofTendstoReal (ρ := η) (ρs := ηs) hηs K hK
  have hmem : ∀ n, c n * t ∈ K := by
    intro n
    change -(B * |t|) ≤ c n * t ∧ c n * t ≤ B * |t|
    have hmul : |c n * t| ≤ B * |t| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hBound n) (abs_nonneg t)
    exact abs_le.mp hmul
  have hct : Tendsto (fun n ↦ c n * t) atTop (𝓝 (cLim * t)) :=
    hc.mul_const t
  have hctWithin : Tendsto (fun n ↦ c n * t) atTop (𝓝[K] (cLim * t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hct, Filter.Eventually.of_forall hmem⟩
  have hchar :
      Tendsto (fun n ↦ charFun (ηs n : Measure ℝ) (c n * t)) atTop
        (𝓝 (charFun (η : Measure ℝ) (cLim * t))) :=
    huni.tendsto_comp
      ((MeasureTheory.continuous_charFun (μ := (η : Measure ℝ))).continuousAt.continuousWithinAt)
      hctWithin
  have hdt : Tendsto (fun n ↦ d n * t) atTop (𝓝 (dLim * t)) :=
    hd.mul_const t
  have hphaseArg :
      Tendsto (fun n ↦ (((d n * t : ℝ) : ℂ) * Complex.I)) atTop
        (𝓝 ((((dLim * t : ℝ) : ℂ) * Complex.I))) := by
    have hrealToComplex :
        Tendsto (fun n ↦ ((d n * t : ℝ) : ℂ)) atTop (𝓝 ((dLim * t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hdt
    exact hrealToComplex.mul_const Complex.I
  have hphase :
      Tendsto (fun n ↦ Complex.exp ((((d n * t : ℝ) : ℂ) * Complex.I))) atTop
        (𝓝 (Complex.exp ((((dLim * t : ℝ) : ℂ) * Complex.I)))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp hphaseArg
  -- Proof comment: after the moving-frequency convergence is established, the affine
  -- characteristic-function identity reduces the target to a product of the transported
  -- characteristic function and the convergent translation phase.
  convert hchar.mul hphase using 1
  · funext n
    rw [charFun_map_affine_eq]
  · rw [charFun_map_affine_eq]

/-- Helper for Theorem 16.27: weak convergence is stable under affine pushforwards whose slopes
stay in a fixed compact interval and whose coefficients converge. -/
lemma tendstoMapAffineOfTendstoOfCoefficients
    {ηs : ℕ+ → ProbabilityMeasure ℝ} {η : ProbabilityMeasure ℝ}
    {c d : ℕ+ → ℝ} {cLim dLim B : ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hc : Tendsto c atTop (𝓝 cLim))
    (hd : Tendsto d atTop (𝓝 dLim))
    (hBound : ∀ n : ℕ+, |c n| ≤ B) :
    Tendsto (fun n : ℕ+ ↦ map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
      atTop (𝓝 (map η (measurable_affineMap cLim dLim).aemeasurable)) := by
  rw [tendstoPnatAtTopIffSuccPNat] at hηs hc hd ⊢
  -- Proof comment: once the nat-indexed compact-uniform bridge is restored, the `ℕ+` case is
  -- just a reindexing along `Nat.succPNat`.
  exact tendstoMapAffineOfTendstoOfCoefficientsNatCore
    (ηs := fun n : ℕ ↦ ηs (Nat.succPNat n))
    (c := fun n : ℕ ↦ c (Nat.succPNat n))
    (d := fun n : ℕ ↦ d (Nat.succPNat n))
    hηs hc hd (fun n ↦ hBound (Nat.succPNat n))

/-- Helper for Theorem 16.27: a weakly convergent sequence of real probability laws eventually
puts mass greater than `3 / 4` on one fixed bounded open interval. -/
lemma eventuallyLargeOpenIntervalMass_of_tendsto
    {σs : ℕ+ → ProbabilityMeasure ℝ} {σ : ProbabilityMeasure ℝ}
    (hσs : Tendsto σs atTop (𝓝 σ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ n : ℕ+ in atTop,
      ((3 : ENNReal) / 4) <
        ((σs n : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Ioo (-R) R) := by
  have hthreeQuarter_lt_univ : ((3 : ENNReal) / 4) < ((σ : Measure ℝ) Set.univ) := by
    -- Proof comment: the limit law is a probability measure, so the whole space has mass `1`.
    rw [show ((σ : Measure ℝ) Set.univ) = (1 : ENNReal) by simp]
    rw [ENNReal.div_lt_iff (by simp) (by simp), one_mul]
    norm_num
  obtain ⟨K, -, hK_compact, hK_mass⟩ :=
    (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ)).exists_lt_isCompact_of_ne_top
      (by simp) hthreeQuarter_lt_univ
  rcases hK_compact.bddBelow with ⟨l, hl⟩
  rcases hK_compact.bddAbove with ⟨u, hu⟩
  let R : ℝ := max |u| |l| + 1
  have hR_pos : 0 < R := by
    -- Proof comment: enlarge the compact support window by one unit to get an open interval.
    dsimp [R]
    positivity
  have hK_subset : K ⊆ Set.Ioo (-R) R := by
    intro x hxK
    have hlx : l ≤ x := hl hxK
    have hxu : x ≤ u := hu hxK
    have hux : x ≤ |u| := le_trans hxu (le_abs_self u)
    have hlx' : -|l| ≤ x := le_trans (neg_abs_le l) hlx
    constructor
    · change -(max |u| |l| + 1) < x
      have hmax : -max |u| |l| ≤ x := by
        have hneg : -max |u| |l| ≤ -|l| := by
          gcongr
          exact le_max_right |u| |l|
        exact le_trans hneg hlx'
      linarith
    · change x < max |u| |l| + 1
      have hmax : x ≤ max |u| |l| := le_trans hux (le_max_left |u| |l|)
      linarith
  have hR_mass : ((3 : ENNReal) / 4) < ((σ : Measure ℝ) (Set.Ioo (-R) R)) := by
    -- Proof comment: the chosen open interval contains the compact set with mass already
    -- exceeding `3/4`.
    exact lt_of_lt_of_le hK_mass (measure_mono hK_subset)
  have hliminf :
      ((σ : Measure ℝ) (Set.Ioo (-R) R)) ≤
        Filter.liminf (fun n : ℕ+ ↦ ((σs n : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Ioo (-R) R))
          atTop :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hσs isOpen_Ioo
  have hEventual :
      ∀ᶠ n : ℕ+ in atTop,
        ((3 : ENNReal) / 4) < ((σs n : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Ioo (-R) R) := by
    -- Proof comment: Portmanteau upgrades the limit's `> 3/4` mass on this open interval to an
    -- eventual lower bound along the approximating sequence.
    apply Filter.eventually_lt_of_lt_liminf (hu := by isBoundedDefault)
    exact lt_of_lt_of_le hR_mass hliminf
  exact ⟨R, hR_pos, hEventual⟩

/-- Helper for Theorem 16.27: if the affine shift dominates the target radius plus the scaled
source radius, then no point from `(-R, R)` can be mapped into `(-S, S)`. -/
lemma preimageIoo_subset_complIoo_of_absShiftLarge
    {c d M R S : ℝ} (hc_nonneg : 0 ≤ c) (hc_le : c ≤ M) (_hR_nonneg : 0 ≤ R)
    (_hS_nonneg : 0 ≤ S)
    (hd_large : S + M * R < |d|) :
    (fun x : ℝ ↦ c * x + d) ⁻¹' Set.Ioo (-S) S ⊆ (Set.Ioo (-R) R)ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_Ioo]
  rintro ⟨hx_left, hx_right⟩
  have hx_abs : |x| < R := by
    -- Proof comment: rewrite membership in `(-R, R)` as an absolute-value bound.
    rw [abs_lt]
    constructor <;> linarith
  have himage_abs : |c * x + d| < S := by
    -- Proof comment: the image-point assumption is the analogous bound in the target interval.
    simpa [abs_lt] using hx
  have hM_nonneg : 0 ≤ M := le_trans hc_nonneg hc_le
  have hcx : |c * x| ≤ M * R := by
    -- Proof comment: bound the affine linear part using the scale upper bound and `|x| < R`.
    calc
      |c * x| = |c| * |x| := by rw [abs_mul]
      _ = c * |x| := by rw [abs_of_nonneg hc_nonneg]
      _ ≤ M * |x| := mul_le_mul_of_nonneg_right hc_le (abs_nonneg x)
      _ ≤ M * R := mul_le_mul_of_nonneg_left (le_of_lt hx_abs) hM_nonneg
  have hd_small : |d| < S + M * R := by
    -- Proof comment: the triangle inequality shows that a point landing in `(-S, S)` forces the
    -- shift size to be at most the target radius plus the scaled source radius.
    have hd_le : |d| ≤ |c * x + d| + |c * x| := by
      calc
        |d| = |(c * x + d) + (-(c * x))| := by ring_nf
        _ ≤ |c * x + d| + |-(c * x)| := abs_add_le _ _
        _ = |c * x + d| + |c * x| := by simp
    exact lt_of_le_of_lt hd_le (add_lt_add_of_lt_of_le himage_abs hcx)
  exact not_lt_of_ge (le_of_lt hd_small) hd_large

/-- Helper for Theorem 16.27: if the source puts more than `3/4` of its mass on `(-R, R)` and a
large shift keeps the affine image of `(-R, R)` outside `(-S, S)`, then the target mass of
`(-S, S)` is strictly below `1 / 4`. -/
lemma largeShift_imageMass_lt_quarter_of_intervalMass_gt_threeQuarters
    {η ξ : ProbabilityMeasure ℝ} {c d M R S : ℝ}
    (hmap : ξ = map η (measurable_affineMap c d).aemeasurable)
    (hc_nonneg : 0 ≤ c) (hc_le : c ≤ M) (hR_nonneg : 0 ≤ R) (hS_nonneg : 0 ≤ S)
    (hd_large : S + M * R < |d|)
    (hη_mass : ((3 : ENNReal) / 4) < ((η : Measure ℝ) (Set.Ioo (-R) R))) :
    ((ξ : Measure ℝ) (Set.Ioo (-S) S)) < (1 : ENNReal) / 4 := by
  -- Proof comment: rewrite the target interval mass through the affine pushforward and compare
  -- its preimage with the complement of the high-mass source interval.
  rw [hmap, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (measurable_affineMap c d) measurableSet_Ioo]
  have hsubset :
      (fun x : ℝ ↦ c * x + d) ⁻¹' Set.Ioo (-S) S ⊆ (Set.Ioo (-R) R)ᶜ :=
    preimageIoo_subset_complIoo_of_absShiftLarge hc_nonneg hc_le hR_nonneg hS_nonneg hd_large
  have hle :
      ((η : Measure ℝ) ((fun x : ℝ ↦ c * x + d) ⁻¹' Set.Ioo (-S) S)) ≤
        ((η : Measure ℝ) ((Set.Ioo (-R) R)ᶜ)) :=
    measure_mono hsubset
  have hcompl_lt : ((η : Measure ℝ) ((Set.Ioo (-R) R)ᶜ)) < (1 : ENNReal) / 4 := by
    -- Proof comment: a probability law with more than `3/4` mass on an interval has less than
    -- `1/4` mass on its measurable complement.
    by_contra hnot
    have hquarter_le : (1 : ENNReal) / 4 ≤ ((η : Measure ℝ) ((Set.Ioo (-R) R)ᶜ)) :=
      not_lt.mp hnot
    have hgt :
        (1 : ENNReal) <
          ((η : Measure ℝ) (Set.Ioo (-R) R)) + ((η : Measure ℝ) ((Set.Ioo (-R) R)ᶜ)) := by
      have hsum : ((3 : ENNReal) / 4) + ((1 : ENNReal) / 4) = 1 := by
        rw [← ENNReal.add_div]
        norm_num
        rw [ENNReal.div_self]
        · norm_num
        · simp
      calc
        (1 : ENNReal) = ((3 : ENNReal) / 4) + ((1 : ENNReal) / 4) := by
          simpa using hsum.symm
        _ < ((η : Measure ℝ) (Set.Ioo (-R) R)) + ((η : Measure ℝ) ((Set.Ioo (-R) R)ᶜ)) :=
          ENNReal.add_lt_add_of_lt_of_le (by finiteness) hη_mass hquarter_le
    have hone :
        ((η : Measure ℝ) (Set.Ioo (-R) R)) + ((η : Measure ℝ) ((Set.Ioo (-R) R)ᶜ)) =
          (1 : ENNReal) := by
      simpa using
        (measure_add_measure_compl (μ := (η : Measure ℝ)) (s := Set.Ioo (-R) R) measurableSet_Ioo)
    have : (1 : ENNReal) < 1 := by
      have hgt' :
          (1 : ENNReal) <
            ((η : Measure ℝ) (Set.Ioo (-R) R)) + ((η : Measure ℝ) ((Set.Ioo (-R) R)ᶜ)) := hgt
      rw [hone] at hgt'
      exact hgt'
    exact (lt_irrefl (1 : ENNReal)) this
  exact lt_of_le_of_lt hle hcompl_lt

/-- Helper for Theorem 16.27: once the affine scales are eventually bounded above, weak
convergence forces the affine shifts to stay eventually bounded as well. -/
lemma eventuallyBoundedAffineShiftOfBoundedScales
    {ηs ξs : ℕ+ → ProbabilityMeasure ℝ} {η ξ : ProbabilityMeasure ℝ}
    {c d : ℕ+ → ℝ} {M : ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hξs : Tendsto ξs atTop (𝓝 ξ))
    (hfac : ∀ n : ℕ+, ξs n = map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
    (hc_pos : ∀ n : ℕ+, 0 < c n)
    (hScale : ∀ᶠ n : ℕ+ in atTop, c n ≤ M) :
    ∃ D : ℝ, ∀ᶠ n : ℕ+ in atTop, |d n| ≤ D := by
  obtain ⟨R, hR_pos, hη_mass⟩ := eventuallyLargeOpenIntervalMass_of_tendsto hηs
  obtain ⟨S, hS_pos, hξ_mass⟩ := eventuallyLargeOpenIntervalMass_of_tendsto hξs
  refine ⟨S + M * R, ?_⟩
  -- Proof comment: if the shifts were frequently larger than the target radius plus the scaled
  -- source radius, the affine image would miss most of the target interval, contradicting the
  -- eventual `> 3/4` target mass there.
  by_contra hD
  have hfreq :
      ∃ᶠ n : ℕ+ in atTop, S + M * R < |d n| := by
    by_contra hnot
    have hEventuallyNot : ∀ᶠ n : ℕ+ in atTop, ¬ S + M * R < |d n| :=
      Filter.not_frequently.mp hnot
    exact hD (by simpa [not_lt] using hEventuallyNot)
  have hbad :
      ∃ᶠ n : ℕ+ in atTop,
        S + M * R < |d n| ∧
          ((3 : ENNReal) / 4) < ((ηs n : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Ioo (-R) R) ∧
          ((3 : ENNReal) / 4) < ((ξs n : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Ioo (-S) S) ∧
          c n ≤ M := by
    refine (hfreq.and_eventually (hη_mass.and (hξ_mass.and hScale))).mono ?_
    intro n hn
    rcases hn with ⟨hdn, hηn, hξn, hc_le⟩
    exact ⟨hdn, hηn, hξn, hc_le⟩
  rcases hbad.exists with ⟨n, hdn, hηn, hξn, hc_le⟩
  have hsmall :
      (((ξs n : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Ioo (-S) S)) < (1 : ENNReal) / 4 :=
    largeShift_imageMass_lt_quarter_of_intervalMass_gt_threeQuarters
      (η := ηs n) (ξ := ξs n) (c := c n) (d := d n) (M := M) (R := R) (S := S)
      (hmap := hfac n) (hc_nonneg := (hc_pos n).le) (hc_le := hc_le) (hR_nonneg := hR_pos.le)
      (hS_nonneg := hS_pos.le) (hd_large := hdn) (hη_mass := hηn)
  have hImpossible : ¬ (((3 : ENNReal) / 4) < (1 : ENNReal) / 4) := by
    have hquarter : ((1 : ENNReal) / 4) ≤ ((3 : ENNReal) / 4) := by
      calc
        (1 : ENNReal) / 4 ≤ (1 : ENNReal) / 4 + (2 : ENNReal) / 4 := by
          exact le_add_of_nonneg_right (by positivity)
        _ = (3 : ENNReal) / 4 := by
          rw [← ENNReal.add_div]
          norm_num
    exact not_lt_of_ge hquarter
  exact hImpossible (lt_trans hξn hsmall)

/-- Helper for Theorem 16.27: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
`atTop` limit. -/
private theorem tendsto_pnat_atTop_iff_succPNat {β : Type*} [TopologicalSpace β]
    {f : ℕ+ → β} {l : Filter β} :
    Tendsto f atTop l ↔ Tendsto (fun n : ℕ ↦ f (Nat.succPNat n)) atTop l := by
  constructor
  · intro hf
    -- Proof comment: compose the `ℕ+`-indexed limit with the order isomorphism `ℕ ≃o ℕ+`.
    simpa [OrderIso.pnatIsoNat_symm_apply] using hf.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  · intro hf
    -- Proof comment: compose the shifted sequence with `PNat.natPred` to recover the original
    -- `ℕ+` indexing.
    have hcomp := hf.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Theorem 16.27: the affine-pushforward weak-continuity lemma also holds for
nat-indexed sequences. -/
private lemma tendstoMapAffineOfTendstoOfCoefficientsNat
    {ηs : ℕ → ProbabilityMeasure ℝ} {η : ProbabilityMeasure ℝ}
    {c d : ℕ → ℝ} {cLim dLim B : ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hc : Tendsto c atTop (𝓝 cLim))
    (hd : Tendsto d atTop (𝓝 dLim))
    (hBound : ∀ n : ℕ, |c n| ≤ B) :
    Tendsto (fun n : ℕ ↦ map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
      atTop (𝓝 (map η (measurable_affineMap cLim dLim).aemeasurable)) := by
  -- Proof comment: this is exactly the nat-indexed core continuity lemma proved above.
  exact tendstoMapAffineOfTendstoOfCoefficientsNatCore hηs hc hd hBound

/-- Helper for Theorem 16.27: if the affine scales converge to `0`, then every fixed-frequency
characteristic-function norm of the affine images converges to `1`. -/
lemma tendstoCharFunNormOneOfTendstoAffineScalesZero
    {ηs ξs : ℕ → ProbabilityMeasure ℝ} {η : ProbabilityMeasure ℝ}
    {c d : ℕ → ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hfac : ∀ n, ξs n = map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
    (hc0 : Tendsto c atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n ↦ ‖charFun (ξs n : Measure ℝ) t‖) atTop (𝓝 1) := by
  let K : Set ℝ := Set.Icc (-|t|) |t|
  have hK : IsCompact K := isCompact_Icc
  have huni :
      TendstoUniformlyOn (fun n s ↦ charFun (ηs n : Measure ℝ) s)
        (charFun (η : Measure ℝ)) atTop K :=
    charFunTendstoUniformlyOn_ofTendstoReal (ρ := η) (ρs := ηs) hηs K hK
  have hsmall : ∀ᶠ n in atTop, c n ∈ Set.Ioo (-1 : ℝ) 1 :=
    hc0 (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1))
  have hmem : ∀ᶠ n in atTop, c n * t ∈ K := by
    filter_upwards [hsmall] with n hn
    change -|t| ≤ c n * t ∧ c n * t ≤ |t|
    have habs : |c n| < 1 := abs_lt.mpr hn
    have hmul : |c n * t| ≤ |t| := by
      rw [abs_mul]
      simpa [mul_comm] using
        (mul_le_of_le_one_right (abs_nonneg t) (le_of_lt habs) : |t| * |c n| ≤ |t|)
    exact abs_le.mp hmul
  have hct : Tendsto (fun n ↦ c n * t) atTop (𝓝 (0 * t)) :=
    hc0.mul_const t
  have hctWithin : Tendsto (fun n ↦ c n * t) atTop (𝓝[K] (0 * t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hct, hmem⟩
  have hchar :
      Tendsto (fun n ↦ charFun (ηs n : Measure ℝ) (c n * t)) atTop
        (𝓝 (charFun (η : Measure ℝ) (0 * t))) :=
    huni.tendsto_comp
      ((MeasureTheory.continuous_charFun (μ := (η : Measure ℝ))).continuousAt.continuousWithinAt)
      hctWithin
  have hnorm :
      Tendsto (fun n ↦ ‖charFun (ηs n : Measure ℝ) (c n * t)‖) atTop (𝓝 1) := by
    simpa using hchar.norm
  -- Proof comment: take norms in the affine characteristic-function identity to remove the
  -- translation phase, whose complex exponential has norm `1`.
  convert hnorm using 1
  ext n
  rw [hfac n, charFun_map_affine_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Helper for Theorem 16.27: if the affine scales converge to `0`, every weak limit of the
affine images is a Dirac mass. -/
lemma eqDiracProbaOfTendstoAffineScalesZero
    {ηs ξs : ℕ → ProbabilityMeasure ℝ} {η ξ : ProbabilityMeasure ℝ}
    {c d : ℕ → ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hξs : Tendsto ξs atTop (𝓝 ξ))
    (hfac : ∀ n, ξs n = map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
    (hc0 : Tendsto c atTop (𝓝 0)) :
    ∃ x : ℝ, ξ = diracProba x := by
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ht_antitone : Antitone fun k ↦ |t k| := by
    intro m n hmn
    -- Proof comment: the reciprocal test sequence decreases monotonically to `0`.
    simp only [t]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      (Nat.one_div_le_one_div (α := ℝ) hmn)
  have ht_zero : Tendsto (fun k ↦ |t k|) atTop (𝓝 0) := by
    -- Proof comment: the same reciprocal sequence tends to `0`.
    have hone :
        Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun k : ℕ ↦ t k) atTop (𝓝 (0 : ℝ)) := by
      simpa [t] using hone
    convert ht using 1
    ext k
    have hk : 0 ≤ t k := by
      dsimp [t]
      positivity
    exact abs_of_nonneg hk
  have ht_nonzero : ∀ k, t k ≠ 0 := by
    intro k
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp [t, hk]
  have hξ_char := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hξs
  have hφ_unit : ∀ k, ‖charFun (ξ : Measure ℝ) (t k)‖ = 1 := by
    intro k
    have hlimitNorm :
        Tendsto (fun n ↦ ‖charFun (ξs n : Measure ℝ) (t k)‖) atTop
          (𝓝 ‖charFun (ξ : Measure ℝ) (t k)‖) :=
      (hξ_char (t k)).norm
    have hnormOne :
        Tendsto (fun n ↦ ‖charFun (ξs n : Measure ℝ) (t k)‖) atTop (𝓝 1) :=
      tendstoCharFunNormOneOfTendstoAffineScalesZero hηs hfac hc0 (t k)
    exact tendsto_nhds_unique hlimitNorm hnormOne
  obtain ⟨x, hx⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  refine ⟨x, ?_⟩
  -- Proof comment: upgrade the measure-level Dirac conclusion to the probability-measure owner.
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hx

/-- Helper for Theorem 16.27: a nat-indexed affine factorization can be inverted pointwise when
all slopes are positive. -/
private lemma inverseAffineFactorizationNat
    {ηs ξs : ℕ → ProbabilityMeasure ℝ} {c d : ℕ → ℝ}
    (hc_pos : ∀ n, 0 < c n)
    (hfac : ∀ n, ξs n = map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable) :
    ∀ n,
      ηs n =
        map (ξs n) (measurable_affineMap ((c n)⁻¹) (-((c n)⁻¹ * d n))).aemeasurable := by
  intro n
  -- Proof comment: invert the pointwise affine factorization using the explicit inverse affine
  -- map with slope `(c n)⁻¹`.
  exact eq_map_inverse_affine_of_eq_map_affine (hc := ne_of_gt (hc_pos n)) (h := hfac n)

/-- Helper for Theorem 16.27: if the target weak limit is non-Dirac, then nat-indexed affine
scales cannot drift to `0` along a subsequence. -/
private lemma eventuallyAffineScales_boundedBelowOfNonDiracTargetNat
    {ηs ξs : ℕ → ProbabilityMeasure ℝ} {η ξ : ProbabilityMeasure ℝ}
    {c d : ℕ → ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hξs : Tendsto ξs atTop (𝓝 ξ))
    (hfac : ∀ n, ξs n = map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
    (hc_pos : ∀ n, 0 < c n)
    (hξ_nontrivial : ∀ x : ℝ, ξ ≠ diracProba x) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ n in atTop, m ≤ c n := by
  by_contra hbound
  have hfreq :
      ∀ m : ℕ, ∃ᶠ n in atTop, c n < 1 / ((m : ℝ) + 1) := by
    intro m
    have hm_pos : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hnot_event :
        ¬ ∀ᶠ n in atTop, 1 / ((m : ℝ) + 1) ≤ c n := by
      intro hm_event
      exact hbound ⟨1 / ((m : ℝ) + 1), hm_pos, hm_event⟩
    -- Proof comment: if no positive eventual lower bound exists, then every reciprocal threshold
    -- `1 / (m + 1)` is violated frequently.
    simpa [not_le] using Filter.not_eventually.1 hnot_event
  obtain ⟨φ, hφ_mono, hφ_small⟩ := Filter.extraction_forall_of_frequently hfreq
  have hcφ_zero : Tendsto (fun m ↦ c (φ m)) atTop (𝓝 0) := by
    -- Proof comment: the extracted subsequence is squeezed between `0` and the reciprocal test
    -- sequence, so its scales converge to `0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat ?_ ?_
    · intro m
      exact (hc_pos (φ m)).le
    · intro m
      exact le_of_lt (hφ_small m)
  have hη_sub : Tendsto (fun m ↦ ηs (φ m)) atTop (𝓝 η) :=
    hηs.comp hφ_mono.tendsto_atTop
  have hξ_sub : Tendsto (fun m ↦ ξs (φ m)) atTop (𝓝 ξ) :=
    hξs.comp hφ_mono.tendsto_atTop
  obtain ⟨x, hx⟩ :=
    eqDiracProbaOfTendstoAffineScalesZero
      (ηs := fun m ↦ ηs (φ m))
      (ξs := fun m ↦ ξs (φ m))
      (c := fun m ↦ c (φ m))
      (d := fun m ↦ d (φ m))
      hη_sub hξ_sub (fun m ↦ hfac (φ m)) hcφ_zero
  exact hξ_nontrivial x hx

/-- Helper for Theorem 16.27: if the source weak limit is non-Dirac, then nat-indexed affine
scales cannot diverge to `+∞` along a subsequence. -/
private lemma eventuallyAffineScales_boundedAboveOfNonDiracSourceNat
    {ηs ξs : ℕ → ProbabilityMeasure ℝ} {η ξ : ProbabilityMeasure ℝ}
    {c d : ℕ → ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hξs : Tendsto ξs atTop (𝓝 ξ))
    (hfac : ∀ n, ξs n = map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
    (hc_pos : ∀ n, 0 < c n)
    (hη_nontrivial : ∀ x : ℝ, η ≠ diracProba x) :
    ∃ M : ℝ, ∀ᶠ n in atTop, c n ≤ M := by
  have hinvfac :
      ∀ n,
        ηs n =
          map (ξs n) (measurable_affineMap ((c n)⁻¹) (-((c n)⁻¹ * d n))).aemeasurable :=
    inverseAffineFactorizationNat hc_pos hfac
  obtain ⟨m, hm_pos, hm_event⟩ :=
    eventuallyAffineScales_boundedBelowOfNonDiracTargetNat
      (ηs := ξs) (ξs := ηs) (η := ξ) (ξ := η)
      (c := fun n ↦ (c n)⁻¹) (d := fun n ↦ -((c n)⁻¹ * d n))
      hξs hηs hinvfac (fun n ↦ inv_pos.mpr (hc_pos n)) hη_nontrivial
  refine ⟨m⁻¹, ?_⟩
  -- Proof comment: apply the lower-bound lemma to the inverse affine factorization and convert
  -- the eventual bound on `(c n)⁻¹` into an eventual upper bound on `c n`.
  filter_upwards [hm_event] with n hn
  have hc_ne : c n ≠ 0 := ne_of_gt (hc_pos n)
  have hmul : m * c n ≤ 1 := by
    calc
      m * c n ≤ (c n)⁻¹ * c n := by
        exact mul_le_mul_of_nonneg_right hn (hc_pos n).le
      _ = 1 := by field_simp [hc_ne]
  have hmul' : c n * m ≤ 1 := by
    simpa [mul_comm] using hmul
  have hle : c n ≤ 1 / m := (le_div_iff₀ hm_pos).2 hmul'
  simpa [one_div] using hle

/-- Helper for Theorem 16.27: non-Dirac weak limits force the affine scales to stay in one
compact positive interval. -/
lemma eventuallyBoundedAffineScalesOfNonDiracLimits
    {ηs ξs : ℕ+ → ProbabilityMeasure ℝ} {η ξ : ProbabilityMeasure ℝ}
    {c d : ℕ+ → ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hξs : Tendsto ξs atTop (𝓝 ξ))
    (hfac : ∀ n : ℕ+, ξs n = map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
    (hc_pos : ∀ n : ℕ+, 0 < c n)
    (hη_nontrivial : ∀ x : ℝ, η ≠ diracProba x)
    (hξ_nontrivial : ∀ x : ℝ, ξ ≠ diracProba x) :
    ∃ m M : ℝ, 0 < m ∧ ∀ᶠ n in atTop, m ≤ c n ∧ c n ≤ M := by
  have hηs_nat : Tendsto (fun n : ℕ ↦ ηs (Nat.succPNat n)) atTop (𝓝 η) :=
    (tendsto_pnat_atTop_iff_succPNat).1 hηs
  have hξs_nat : Tendsto (fun n : ℕ ↦ ξs (Nat.succPNat n)) atTop (𝓝 ξ) :=
    (tendsto_pnat_atTop_iff_succPNat).1 hξs
  obtain ⟨m, hm_pos, hm_event⟩ :=
    eventuallyAffineScales_boundedBelowOfNonDiracTargetNat
      (ηs := fun n : ℕ ↦ ηs (Nat.succPNat n))
      (ξs := fun n : ℕ ↦ ξs (Nat.succPNat n))
      (c := fun n : ℕ ↦ c (Nat.succPNat n))
      (d := fun n : ℕ ↦ d (Nat.succPNat n))
      hηs_nat hξs_nat
      (fun n ↦ hfac (Nat.succPNat n))
      (fun n ↦ hc_pos (Nat.succPNat n))
      hξ_nontrivial
  obtain ⟨M, hM_event⟩ :=
    eventuallyAffineScales_boundedAboveOfNonDiracSourceNat
      (ηs := fun n : ℕ ↦ ηs (Nat.succPNat n))
      (ξs := fun n : ℕ ↦ ξs (Nat.succPNat n))
      (c := fun n : ℕ ↦ c (Nat.succPNat n))
      (d := fun n : ℕ ↦ d (Nat.succPNat n))
      hηs_nat hξs_nat
      (fun n ↦ hfac (Nat.succPNat n))
      (fun n ↦ hc_pos (Nat.succPNat n))
      hη_nontrivial
  refine ⟨m, M, hm_pos, ?_⟩
  have hnat :
      ∀ᶠ n : ℕ in atTop, m ≤ c (Nat.succPNat n) ∧ c (Nat.succPNat n) ≤ M :=
    (hm_event.and hM_event).mono fun _ hn ↦ ⟨hn.1, hn.2⟩
  -- Proof comment: the `ℕ+` statement is the same eventual bound transported back through the
  -- order isomorphism `ℕ ≃o ℕ+`.
  rw [← OrderIso.pnatIsoNat.symm.map_atTop]
  simpa [OrderIso.pnatIsoNat_symm_apply] using hnat

/-- Helper for Theorem 16.27: a weak limit of affine factorizations with positive slopes is
itself an affine image once the convergence-of-types boundedness step is supplied. -/
lemma existsAffineLimitOfTendstoAffineFactorizations
    {ηs ξs : ℕ+ → ProbabilityMeasure ℝ} {η ξ : ProbabilityMeasure ℝ}
    {c d : ℕ+ → ℝ}
    (hηs : Tendsto ηs atTop (𝓝 η))
    (hξs : Tendsto ξs atTop (𝓝 ξ))
    (hfac : ∀ n : ℕ+, ξs n = map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable)
    (hc_pos : ∀ n : ℕ+, 0 < c n)
    (hη_nontrivial : ∀ x : ℝ, η ≠ diracProba x)
    (hξ_nontrivial : ∀ x : ℝ, ξ ≠ diracProba x) :
    ∃ cLim dLim, 0 < cLim ∧ ξ = map η (measurable_affineMap cLim dLim).aemeasurable := by
  -- Route correction: the scale-boundedness package is now closed, so only the compactness step
  -- remains. Tail the coefficient sequence into one compact rectangle using
  -- `eventuallyBoundedAffineScalesOfNonDiracLimits` and
  -- `eventuallyBoundedAffineShiftOfBoundedScales`, extract a convergent subsequence of pairs, and
  -- identify the affine weak limit with `tendstoMapAffineOfTendstoOfCoefficients`.
  obtain ⟨m, M, hm_pos, hScale⟩ :=
    eventuallyBoundedAffineScalesOfNonDiracLimits
      (ηs := ηs) (ξs := ξs) (c := c) (d := d)
      hηs hξs hfac hc_pos hη_nontrivial hξ_nontrivial
  obtain ⟨D, hShift⟩ :=
    eventuallyBoundedAffineShiftOfBoundedScales
      (ηs := ηs) (ξs := ξs) (c := c) (d := d)
      hηs hξs hfac hc_pos (hScale.mono fun _ hn ↦ hn.2)
  have hBox :
      ∀ᶠ n : ℕ+ in atTop, m ≤ c n ∧ c n ≤ M ∧ |d n| ≤ D := by
    -- Proof comment: intersect the eventual scale and shift bounds to get one compact rectangle.
    filter_upwards [hScale, hShift] with n hnScale hnShift
    exact ⟨hnScale.1, hnScale.2, hnShift⟩
  have hBoxNat :
      ∀ᶠ n : ℕ in atTop,
        m ≤ c (Nat.succPNat n) ∧ c (Nat.succPNat n) ≤ M ∧ |d (Nat.succPNat n)| ≤ D :=
    OrderIso.pnatIsoNat.symm.tendsto_atTop.eventually hBox
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hBoxNat
  let K : Set (ℝ × ℝ) := Set.Icc m M ×ˢ Set.Icc (-D) D
  have hKCompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hTailMem : ∀ n : ℕ, (c (Nat.succPNat (N + n)), d (Nat.succPNat (N + n))) ∈ K := by
    intro n
    have hn := hN (N + n) (Nat.le_add_right N n)
    exact ⟨⟨hn.1, hn.2.1⟩, by simpa [Set.mem_Icc, abs_le] using hn.2.2⟩
  obtain ⟨uLim, huLimK, φ, hφmono, hφtendsto⟩ := hKCompact.tendsto_subseq hTailMem
  have hIndexTendsto : Tendsto (fun n : ℕ ↦ N + φ n) atTop atTop := by
    -- Proof comment: the extracted subsequence still tends to infinity after reinstating the tail.
    simpa [add_comm] using (tendsto_add_atTop_nat N).comp hφmono.tendsto_atTop
  have hηsNat : Tendsto (fun n : ℕ ↦ ηs (Nat.succPNat n)) atTop (𝓝 η) :=
    (tendsto_pnat_atTop_iff_succPNat).1 hηs
  have hξsNat : Tendsto (fun n : ℕ ↦ ξs (Nat.succPNat n)) atTop (𝓝 ξ) :=
    (tendsto_pnat_atTop_iff_succPNat).1 hξs
  have hηSub :
      Tendsto (fun n : ℕ ↦ ηs (Nat.succPNat (N + φ n))) atTop (𝓝 η) := by
    simpa [Function.comp, add_comm] using hηsNat.comp hIndexTendsto
  have hξSub :
      Tendsto (fun n : ℕ ↦ ξs (Nat.succPNat (N + φ n))) atTop (𝓝 ξ) := by
    simpa [Function.comp, add_comm] using hξsNat.comp hIndexTendsto
  have hcSub :
      Tendsto (fun n : ℕ ↦ c (Nat.succPNat (N + φ n))) atTop (𝓝 uLim.1) := by
    -- Proof comment: the compact-box subsequence gives convergent scale coefficients.
    simpa [K] using (continuous_fst.tendsto uLim).comp hφtendsto
  have hdSub :
      Tendsto (fun n : ℕ ↦ d (Nat.succPNat (N + φ n))) atTop (𝓝 uLim.2) := by
    -- Proof comment: the same subsequence gives convergent shift coefficients.
    simpa [K] using (continuous_snd.tendsto uLim).comp hφtendsto
  have hBoundSub :
      ∀ n : ℕ, |c (Nat.succPNat (N + φ n))| ≤ max |m| |M| := by
    intro n
    exact abs_le_max_abs_abs (hTailMem (φ n)).1.1 (hTailMem (φ n)).1.2
  have hMapSub :
      Tendsto
        (fun n : ℕ ↦ ξs (Nat.succPNat (N + φ n)))
        atTop
        (𝓝 (map η (measurable_affineMap uLim.1 uLim.2).aemeasurable)) := by
    -- Proof comment: once the coefficient subsequence converges inside the compact box, the
    -- affine-image continuity lemma identifies the weak limit of the corresponding affine images.
    convert
      tendstoMapAffineOfTendstoOfCoefficientsNat
        (ηs := fun n : ℕ ↦ ηs (Nat.succPNat (N + φ n)))
        (c := fun n : ℕ ↦ c (Nat.succPNat (N + φ n)))
        (d := fun n : ℕ ↦ d (Nat.succPNat (N + φ n)))
        hηSub hcSub hdSub hBoundSub
      using 1
    funext n
    exact hfac (Nat.succPNat (N + φ n))
  have huLim_pos : 0 < uLim.1 := lt_of_lt_of_le hm_pos huLimK.1.1
  refine ⟨uLim.1, uLim.2, huLim_pos, ?_⟩
  -- Proof comment: the same subsequence of affine factorizations converges to both `ξ` and the
  -- affine image of `η`, so uniqueness of limits identifies the two laws.
  exact tendsto_nhds_unique hξSub hMapSub

-- Proof sketch: apply the limit theorem for domains of attraction to any law `ν` whose affinely
-- normalized convolution powers converge weakly to the nontrivial limit law `μ`.
/-- Any nontrivial real probability law with a nonempty domain of attraction is broadly stable. -/
theorem isStableInBroadSense_of_mem_domainOfAttraction
    (hμ_nontrivial : ∀ x : ℝ, μ ≠ diracProba x) (hν : ν ∈ domainOfAttraction μ) :
    IsStableInBroadSense μ := by
  rcases (mem_domainOfAttraction_iff μ ν).1 hν with ⟨a, b, ha, hTendsto⟩
  have hAffineLimit :
      ∀ k : ℕ+, ∃ cLim dLim, 0 < cLim ∧
        μ = map (μ ^ (k : ℕ)) (measurable_affineMap cLim dLim).aemeasurable := by
    intro k
    let ηs : ℕ+ → ProbabilityMeasure ℝ := fun n ↦ (normalizedConvolutionLaw ν a b n) ^ (k : ℕ)
    let ξs : ℕ+ → ProbabilityMeasure ℝ := fun n ↦ normalizedConvolutionLaw ν a b (k * n)
    let c : ℕ+ → ℝ := fun n ↦ a n / a (k * n)
    let d : ℕ+ → ℝ := fun n ↦ (((k : ℝ) * b n) - b (k * n)) / a (k * n)
    have hηs : Tendsto ηs atTop (𝓝 (μ ^ (k : ℕ))) := by
      -- Proof comment: the domain-of-attraction limit survives passage to the fixed `k`th power.
      simpa [ηs] using tendsto_pow_of_tendsto (ρ := fun n : ℕ+ ↦ normalizedConvolutionLaw ν a b n)
        hTendsto k
    have hTendstoNat :
        Tendsto (fun n : ℕ ↦ normalizedConvolutionLaw ν a b (Nat.succPNat n)) atTop (𝓝 μ) :=
      (tendsto_pnat_atTop_iff_succPNat).1 hTendsto
    have hMulNat :
        Tendsto (fun n : ℕ ↦ OrderIso.pnatIsoNat (k * Nat.succPNat n)) atTop atTop := by
      -- Proof comment: multiplication by the fixed block size becomes a strict-monotone nat
      -- reindex after transporting through `ℕ ≃o ℕ+`.
      have hMulNatStrict : StrictMono fun n : ℕ ↦ OrderIso.pnatIsoNat (k * Nat.succPNat n) := by
        intro m n hmn
        exact
          OrderIso.pnatIsoNat.strictMono
            (by
              exact_mod_cast Nat.mul_lt_mul_of_pos_left (Nat.succ_lt_succ hmn) k.pos)
      exact hMulNatStrict.tendsto_atTop
    have hξs : Tendsto ξs atTop (𝓝 μ) := by
      -- Proof comment: the block-normalized sequence is just the original domain witness along the
      -- cofinal subsequence `n ↦ k * n`, expressed on `ℕ` via `OrderIso.pnatIsoNat`.
      rw [tendsto_pnat_atTop_iff_succPNat]
      convert hTendstoNat.comp hMulNat using 1
      funext n
      simp [ξs, Function.comp, OrderIso.pnatIsoNat_apply, PNat.succPNat_natPred]
    have hfac :
        ∀ n : ℕ+, ξs n =
          map (ηs n) (measurable_affineMap (c n) (d n)).aemeasurable := by
      intro n
      -- Proof comment: the block factorization rewrites time `k * n` as an affine image of the
      -- `k`th convolution power of the time-`n` normalization.
      simpa [ηs, ξs, c, d] using
        normalizedConvolutionLaw_blockFactorization (ν := ν) (a := a) (b := b) ha k n
    have hc_pos : ∀ n : ℕ+, 0 < c n := by
      intro n
      -- Proof comment: both scaling sequences in the block factorization are positive.
      exact div_pos (ha n) (ha (k * n))
    have hη_nontrivial : ∀ x : ℝ, μ ^ (k : ℕ) ≠ diracProba x :=
      powNotDiracOfNotDirac hμ_nontrivial k
    exact
      existsAffineLimitOfTendstoAffineFactorizations
        (ηs := ηs) (ξs := ξs) (η := μ ^ (k : ℕ)) (ξ := μ)
        (c := c) (d := d) hηs hξs hfac hc_pos hη_nontrivial hμ_nontrivial
  choose cLim dLim hcLim_pos hμ_map using hAffineLimit
  refine ⟨hμ_nontrivial, ?_⟩
  refine ⟨fun k ↦ (cLim k)⁻¹, fun k ↦ -((cLim k)⁻¹ * dLim k), ?_, ?_⟩
  · intro k
    -- Proof comment: the inverse affine witnesses inherit nonnegative scales from the positive
    -- limiting scales.
    exact inv_nonneg.mpr (hcLim_pos k).le
  · intro k
    -- Proof comment: invert the affine representation `μ = map (μ ^ k) A` to get the required
    -- broad-stability factorization of `μ ^ k`.
    exact
      eq_map_inverse_affine_of_eq_map_affine
        (hc := ne_of_gt (hcLim_pos k)) (h := hμ_map k)

-- Proof sketch: extract the scale-and-shift witnesses from `IsStableInBroadSense` and use the
-- inverse affine normalizations to make the normalized convolution powers of `μ` converge to `μ`
-- itself.
/-- A broadly stable real probability law belongs to its own domain of attraction. -/
theorem self_mem_domainOfAttraction_of_isStableInBroadSense
    (hμ : IsStableInBroadSense μ) :
    μ ∈ domainOfAttraction μ := by
  rcases IsStableInBroadSense.exists_scale_shift hμ with ⟨a, d, ha_nonneg, hpow⟩
  have ha_pos : ∀ n : ℕ+, 0 < a n :=
    affineScale_pos_of_isStableInBroadSense hμ ha_nonneg hpow
  refine (mem_domainOfAttraction_iff μ μ).2 ?_
  refine ⟨a, d, ha_pos, ?_⟩
  have hself : ∀ n : ℕ+, normalizedConvolutionLaw μ a d n = μ :=
    normalizedConvolutionLaw_eq_self_of_affinePow (μ := μ) (a := a) (d := d) ha_pos hpow
  -- Proof comment: the original broad-stability witness already makes every normalized law equal
  -- to `μ`, so the convergence is constant.
  have hselfFun :
      (fun n : ℕ+ ↦ normalizedConvolutionLaw μ a d n) = fun _ : ℕ+ ↦ μ := by
    funext n
    exact hself n
  simp [hselfFun]

-- Proof sketch: combine the membership-to-stability bridge with self-membership of a broadly
-- stable law.
/-- Theorem 16.27: for a nontrivial real probability law, the domain of attraction is nonempty if
and only if the law is stable in the broad sense. -/
theorem domainOfAttraction_nonempty_iff_isStableInBroadSense
    (hμ_nontrivial : ∀ x : ℝ, μ ≠ diracProba x) :
    Set.Nonempty (domainOfAttraction μ) ↔ IsStableInBroadSense μ := by
  constructor
  · rintro ⟨ν, hν⟩
    exact isStableInBroadSense_of_mem_domainOfAttraction hμ_nontrivial hν
  · intro hμ
    exact ⟨μ, self_mem_domainOfAttraction_of_isStableInBroadSense hμ⟩

end MeasureTheory.ProbabilityMeasure
