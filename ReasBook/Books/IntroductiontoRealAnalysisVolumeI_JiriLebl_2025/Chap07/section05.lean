/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open Filter Topology

universe u v

section Chap07
section Section05

section

variable {X : Type u} [PseudoMetricSpace X]
variable {Y : Type v} [PseudoMetricSpace Y]

/-- Definition 7.5.1. A function `f : X → Y` between metric spaces is
continuous at `c` if for every `ε > 0` there is `δ > 0` such that
`dist x c < δ` implies `dist (f x) (f c) < ε`. When this holds for every
`c`, the function is continuous. -/
def metricContinuousAt (f : X → Y) (c : X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : X⦄, dist x c < δ → dist (f x) (f c) < ε

/-- The book's ε-δ continuity at a point agrees with mathlib's `ContinuousAt`. -/
theorem metricContinuousAt_iff_continuousAt (f : X → Y) (c : X) :
    metricContinuousAt (X := X) (Y := Y) f c ↔ ContinuousAt f c := by
  simpa [metricContinuousAt] using
    (Metric.continuousAt_iff (f := f) (a := c)).symm

/-- Proposition 7.5.2. A map between metric spaces is continuous at `c` if and
only if every sequence converging to `c` has image sequence converging to
`f c`. -/
theorem continuousAt_iff_tendsto_seq {f : X → Y} {c : X} :
    ContinuousAt f c ↔
      ∀ x : ℕ → X, Tendsto x atTop (𝓝 c) →
        Tendsto (fun n => f (x n)) atTop (𝓝 (f c)) := by
  simpa [ContinuousAt, Function.comp] using
    (tendsto_nhds_iff_seq_tendsto (X := X) (Y := Y) (f := f) (a := c) (b := f c))

/-- A function is (globally) continuous when it is continuous at every point. -/
def metricContinuous (f : X → Y) : Prop :=
  ∀ c : X, metricContinuousAt (X := X) (Y := Y) f c

/-- The book's notion of a continuous function coincides with `Continuous`. -/
theorem metricContinuous_iff_continuous (f : X → Y) :
    metricContinuous (X := X) (Y := Y) f ↔ Continuous f := by
  constructor
  · intro h
    refine (continuous_iff_continuousAt).2 ?_
    intro c
    exact (metricContinuousAt_iff_continuousAt (f := f) (c := c)).1 (h c)
  · intro h c
    have hc : ContinuousAt f c := (continuous_iff_continuousAt).1 h c
    exact (metricContinuousAt_iff_continuousAt (f := f) (c := c)).2 hc

/-- Example 7.5.3. A polynomial on `ℝ × ℝ` (and more generally on finitely many
variables) defines a continuous function. -/
theorem polynomial_two_vars_continuous (p : MvPolynomial (Fin 2) ℝ) :
    Continuous (fun x : Fin 2 → ℝ => MvPolynomial.eval x p) := by
  simpa using (MvPolynomial.continuous_eval (p := p))

theorem polynomial_finite_vars_continuous {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Continuous (fun x : Fin n → ℝ => MvPolynomial.eval x p) := by
  simpa using (MvPolynomial.continuous_eval (p := p))

/-- Example 7.5.4. A complex-valued function on a metric space is continuous at
`c` exactly when its real and imaginary parts are continuous at `c`. -/
theorem continuousAt_complex_iff_real_im {X : Type u} [PseudoMetricSpace X]
    {f : X → ℂ} {c : X} :
    ContinuousAt f c ↔
      ContinuousAt (fun x => Complex.re (f x)) c ∧
      ContinuousAt (fun x => Complex.im (f x)) c := by
  constructor
  · intro h
    constructor
    · -- compose with the continuous real part
      simpa using (Complex.continuous_re.continuousAt.comp (x := c) h)
    · -- compose with the continuous imaginary part
      simpa using (Complex.continuous_im.continuousAt.comp (x := c) h)
  · rintro ⟨hre, him⟩
    -- combine the real and imaginary parts into a product
    have hprod :
        ContinuousAt (fun x => (Complex.re (f x), Complex.im (f x))) c :=
      hre.prodMk him
    have :
        ContinuousAt
          (fun x =>
            Complex.equivRealProdCLM.symm (Complex.re (f x), Complex.im (f x))) c :=
      (Complex.equivRealProdCLM.symm.continuousAt.comp (x := c) hprod)
    simpa [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using this

/-- Lemma 7.5.5. A continuous function maps compact sets to compact sets. -/
lemma compact_image_of_continuous {X : Type u} [PseudoMetricSpace X]
    {Y : Type v} [PseudoMetricSpace Y] {f : X → Y} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) : IsCompact (f '' K) := by
  exact hK.image hf

/-- Theorem 7.5.6. A continuous real-valued function on a nonempty compact
metric space is bounded and attains both its absolute minimum and maximum. -/
theorem continuous_on_compact_real_extrema {X : Type u} [PseudoMetricSpace X]
    [CompactSpace X] [Nonempty X] {f : X → ℝ} (hf : Continuous f) :
    ∃ x_min x_max : X, ∀ x : X, f x_min ≤ f x ∧ f x ≤ f x_max := by
  classical
  have hcompact :
      IsCompact (f '' (Set.univ : Set X)) :=
    compact_image_of_continuous (X := X) (Y := ℝ) (f := f) hf isCompact_univ
  have hnonempty : (f '' (Set.univ : Set X)).Nonempty := by
    obtain ⟨x0⟩ := (inferInstance : Nonempty X)
    exact ⟨f x0, ⟨x0, trivial, rfl⟩⟩
  obtain ⟨ymax, hymax⟩ := hcompact.exists_isGreatest hnonempty
  obtain ⟨ymin, hymin⟩ := hcompact.exists_isLeast hnonempty
  rcases hymax.1 with ⟨x_max, -, rfl⟩
  rcases hymin.1 with ⟨x_min, -, rfl⟩
  refine ⟨x_min, x_max, ?_⟩
  intro x
  have hx : f x ∈ f '' (Set.univ : Set X) := ⟨x, trivial, rfl⟩
  constructor
  · exact hymin.2 hx
  · exact hymax.2 hx

/-- Lemma 7.5.7. A function between metric spaces is continuous at a point
exactly when every open neighborhood of its value has a preimage that is an
open neighborhood of the point. -/
lemma continuousAt_iff_preimage_open_nhds {f : X → Y} {c : X} :
    ContinuousAt f c ↔
      ∀ ⦃U : Set Y⦄, IsOpen U → f c ∈ U →
        ∃ V : Set X, IsOpen V ∧ c ∈ V ∧ V ⊆ f ⁻¹' U := by
  constructor
  · intro hf U hU hfc
    have hpre : f ⁻¹' U ∈ 𝓝 c := hf.preimage_mem_nhds (IsOpen.mem_nhds hU hfc)
    rcases mem_nhds_iff.1 hpre with ⟨V, hVsubset, hVopen, hVc⟩
    exact ⟨V, hVopen, hVc, hVsubset⟩
  · intro hU
    refine Filter.tendsto_def.2 ?_
    intro s hs
    rcases mem_nhds_iff.1 hs with ⟨U, hUsubset, hUopen, hfcU⟩
    rcases hU hUopen hfcU with ⟨V, hVopen, hVc, hVsubset⟩
    have hVmem : V ∈ 𝓝 c := hVopen.mem_nhds hVc
    have hVs : V ⊆ f ⁻¹' s := by
      intro x hx
      exact hUsubset (hVsubset hx)
    exact mem_of_superset hVmem hVs

/-- Theorem 7.5.8. A function between metric spaces is continuous if and only if
for every open set in the codomain, its preimage is open in the domain. -/
theorem continuous_iff_preimage_open {f : X → Y} :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  constructor
  · intro hf U hU
    exact hU.preimage hf
  · intro hU
    refine (continuous_iff_continuousAt).2 ?_
    intro c
    refine (continuousAt_iff_preimage_open_nhds (f := f) (c := c)).2 ?_
    intro U hUopen hfc
    refine ⟨f ⁻¹' U, hU U hUopen, ?_, subset_rfl⟩
    simpa using hfc

/-- Example 7.5.9. For a continuous function, closed sets pull back to closed
sets. In particular, if `f : X → ℝ` is continuous, then its zero set and its
nonnegative set are closed, while the positive set is open. -/
theorem preimage_closed_of_continuous {f : X → Y} (hf : Continuous f)
    {E : Set Y} (hE : IsClosed E) : IsClosed (f ⁻¹' E) := by
  simpa using hE.preimage hf

theorem zero_set_closed_of_continuous {f : X → ℝ} (hf : Continuous f) :
    IsClosed {x : X | f x = 0} := by
  simpa [Set.preimage, Set.mem_singleton_iff] using
    (preimage_closed_of_continuous (X := X) (Y := ℝ) (f := f) hf
      (E := ({0} : Set ℝ)) isClosed_singleton)

theorem nonneg_preimage_closed_of_continuous {f : X → ℝ} (hf : Continuous f) :
    IsClosed {x : X | 0 ≤ f x} := by
  simpa [Set.preimage, Set.mem_Ici] using
    (preimage_closed_of_continuous (X := X) (Y := ℝ) (f := f) hf
      (E := Set.Ici (0 : ℝ)) isClosed_Ici)

theorem pos_preimage_open_of_continuous {f : X → ℝ} (hf : Continuous f) :
    IsOpen {x : X | 0 < f x} := by
  simpa [Set.preimage, Set.mem_Ioi] using
    (hf.isOpen_preimage (s := Set.Ioi (0 : ℝ)) isOpen_Ioi)

/-- Definition 7.5.10. A function between metric spaces is uniformly continuous
if for every `ε > 0` there exists `δ > 0` such that `dist p q < δ` implies
`dist (f p) (f q) < ε`. -/
def metricUniformContinuous (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ ⦃p q : X⦄, dist p q < δ → dist (f p) (f q) < ε

/-- The book's notion of uniform continuity agrees with mathlib's
`UniformContinuous`. -/
theorem metricUniformContinuous_iff_uniformContinuous (f : X → Y) :
    metricUniformContinuous (X := X) (Y := Y) f ↔ UniformContinuous f := by
  simpa [metricUniformContinuous] using
    (Metric.uniformContinuous_iff (f := f)).symm

/-- Theorem 7.5.11. A continuous function from a compact metric space to another
metric space is uniformly continuous. -/
theorem continuous_uniformContinuous_of_compact [CompactSpace X] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
  simpa using
    (CompactSpace.uniformContinuous_of_continuous (f := f) hf)

/-- Proposition 7.5.12. If `f : [a,b] × [c,d] → ℝ` is continuous, then
`g : [c,d] → ℝ` defined by `g y = ∫ x in a..b, f (x,y)` is continuous. -/
theorem intervalIntegral_continuous_on_rectangle {a b c d : ℝ}
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) :
    Continuous (fun y : Set.Icc c d => ∫ x in a..b, f x y) := by
  classical
  -- reuse the parametric interval integral continuity lemma
  have hcont :
      Continuous (Function.uncurry fun (y : Set.Icc c d) (x : ℝ) => f x y) := by
    -- swap coordinates to match `hf`
    have hswap : Continuous fun p : Set.Icc c d × ℝ => ((p.2), (p.1 : ℝ)) := by
      continuity
    simpa [Function.uncurry] using (hf.comp hswap)
  -- apply the library lemma with parameter `y` and variable `x`
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) (f := fun (y : Set.Icc c d) (x : ℝ) => f x y)
      (a₀ := a) (b₀ := b)
      (hf := hcont))

/-- Example 7.5.13. A `K`-Lipschitz map between metric spaces is uniformly
continuous. Conversely, the square root on `[0,1]` is uniformly continuous but
fails to be Lipschitz. -/
theorem lipschitz_uniformContinuous {K : NNReal} {f : X → Y}
    (hf : LipschitzWith K f) : UniformContinuous f := by
  simpa using hf.uniformContinuous

theorem sqrt_uniformContinuous_on_Icc :
    UniformContinuous (fun x : Set.Icc (0 : ℝ) 1 => Real.sqrt x) := by
  simpa using
    (continuous_uniformContinuous_of_compact
      (X := Set.Icc (0 : ℝ) 1) (Y := ℝ)
      (f := fun x => Real.sqrt x)
      (hf := Real.continuous_sqrt.comp continuous_subtype_val))

theorem sqrt_not_Lipschitz_on_Icc :
    ¬ ∃ K : NNReal, LipschitzWith K (fun x : Set.Icc (0 : ℝ) 1 => Real.sqrt x) := by
  classical
  intro h
  rcases h with ⟨K, hK⟩
  have hKge1 : (1 : ℝ) ≤ (K : ℝ) := by
    have h := hK.dist_le_mul (x := ⟨1, by norm_num⟩) (y := ⟨0, by norm_num⟩)
    change dist (Real.sqrt (1 : ℝ)) (Real.sqrt 0) ≤ (K : ℝ) * dist (1 : ℝ) 0 at h
    have hsqrt : dist (Real.sqrt (1 : ℝ)) (Real.sqrt 0) = (1 : ℝ) := by norm_num
    have hdist : dist (1 : ℝ) 0 = (1 : ℝ) := by norm_num
    have : (1 : ℝ) ≤ (K : ℝ) * (1 : ℝ) := by simpa [hsqrt, hdist] using h
    simpa using this
  have hKpos : 0 < (K : ℝ) := lt_of_lt_of_le (by norm_num) hKge1
  set t : ℝ := 1 / (2 * (K : ℝ))
  have ht_pos : 0 < t := by
    have hden_pos : 0 < 2 * (K : ℝ) := mul_pos (by norm_num) hKpos
    exact one_div_pos.mpr hden_pos
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have ht_le_half : t ≤ 1 / 2 := by
    have hden_le : (2 : ℝ) ≤ 2 * (K : ℝ) := by nlinarith
    have htwo_pos : 0 < (2 : ℝ) := by norm_num
    have h := one_div_le_one_div_of_le htwo_pos hden_le
    simpa [t, mul_comm, mul_left_comm, mul_assoc] using h
  have htsq_le_one : t ^ 2 ≤ 1 := by
    have htsq_le_half : t ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith [ht_nonneg, ht_le_half]
    have hhalf_sq_le_one : (1 / 2 : ℝ) ^ 2 ≤ 1 := by norm_num
    exact htsq_le_half.trans hhalf_sq_le_one
  set x0 : Set.Icc (0 : ℝ) 1 := ⟨t ^ 2, by exact ⟨sq_nonneg t, htsq_le_one⟩⟩
  set y0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
  have hineq := hK.dist_le_mul x0 y0
  change dist (Real.sqrt (x0 : ℝ)) (Real.sqrt (y0 : ℝ))
      ≤ (K : ℝ) * dist (x0 : ℝ) (y0 : ℝ) at hineq
  simp [x0, y0] at hineq
  have hineq' : t ≤ (K : ℝ) * t ^ 2 := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg] using hineq
  have hcontr : (1 : ℝ) ≤ (K : ℝ) * t := by
    have hfactor_nonneg : 0 ≤ 1 / t := le_of_lt (one_div_pos.mpr ht_pos)
    have h := mul_le_mul_of_nonneg_left hineq' hfactor_nonneg
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    simpa [pow_two, ht_ne, mul_comm, mul_left_comm, mul_assoc] using h
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hcalc : (K : ℝ) * t = (1 : ℝ) / 2 := by
    unfold t
    field_simp [hKne]
  have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by simpa [hcalc] using hcontr
  linarith

/-- Definition 7.5.14. In a metric space `(X, d)` and subset `S`, a point `p`
is a cluster point of `S` if every open ball around `p` meets `S` at some point
other than `p`. -/
def metricClusterPoint (p : X) (S : Set X) : Prop :=
  ∀ ε > 0, (Metric.ball p ε ∩ (S \ {p})).Nonempty

/-- The book's notion of cluster point agrees with the topological description
as belonging to the closure of `S \ {p}`. -/
theorem metricClusterPoint_iff_mem_closure_diff (p : X) (S : Set X) :
    metricClusterPoint (X := X) p S ↔ p ∈ closure (S \ {p}) := by
  constructor
  · intro hp
    refine (Metric.mem_closure_iff).2 ?_
    intro ε hε
    rcases hp ε hε with ⟨x, hxball, hxSdiff⟩
    refine ⟨x, hxSdiff, ?_⟩
    have : dist x p < ε := by
      simpa [Metric.mem_ball] using hxball
    simpa [dist_comm] using this
  · intro hp ε hε
    rcases (Metric.mem_closure_iff.1 hp) ε hε with ⟨x, hxSdiff, hxdist⟩
    refine ⟨x, ?_, hxSdiff⟩
    have : dist x p < ε := by
      simpa [dist_comm] using hxdist
    simpa [Metric.mem_ball] using this

/-- Definition 7.5.15. For metric spaces `(X, d_X)`, `(Y, d_Y)`, subset `S`,
and cluster point `p` of `S`, a function `f : X → Y` has limit `L` at `p`
along `S` when every punctured neighborhood of `p` in `S` is sent within any
`ε`-ball around `L`. If the limit is unique we write `lim_{x → p} f x = L`. -/
def metricLimitWithin (f : X → Y) (S : Set X) (p : X) (L : Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : X⦄, x ∈ S → x ≠ p → dist x p < δ → dist (f x) L < ε

/-- The ε-δ limit within a set agrees with mathlib's `Tendsto` along the
punctured neighborhood filter. -/
theorem metricLimitWithin_iff_tendsto (f : X → Y) (S : Set X) (p : X) (L : Y) :
    metricLimitWithin (X := X) (Y := Y) f S p L ↔
      Tendsto f (𝓝[S \ {p}] p) (𝓝 L) := by
  constructor
  · intro h
    refine (Metric.tendsto_nhdsWithin_nhds.2 ?_)
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := h ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro x hxSdiff hxdist
    rcases (by
      simpa [Set.mem_diff, Set.mem_singleton_iff] using hxSdiff
      : x ∈ S ∧ x ≠ p) with ⟨hxS, hxne⟩
    exact hδ hxS hxne hxdist
  · intro h ε hε
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.1 h) ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro x hxS hxne hxdist
    have hxSdiff : x ∈ S \ {p} := by
      have : x ∈ S ∧ x ≠ p := ⟨hxS, hxne⟩
      simpa [Set.mem_diff, Set.mem_singleton_iff] using this
    exact hδ hxSdiff hxdist

/-- Proposition 7.5.16. If `p` is a cluster point of `S` and a function has a
limit along `S` at `p`, that limit is unique. -/
theorem metricLimitWithin_unique {S : Set X} {p : X} {f : X → Y} {L₁ L₂ : Y}
    [T2Space Y]
    (hp : metricClusterPoint (X := X) p S)
    (h₁ : metricLimitWithin (X := X) (Y := Y) f S p L₁)
    (h₂ : metricLimitWithin (X := X) (Y := Y) f S p L₂) :
    L₁ = L₂ := by
  have h₁' :
      Tendsto f (𝓝[S \ {p}] p) (𝓝 L₁) :=
    (metricLimitWithin_iff_tendsto (f := f) (S := S) (p := p) (L := L₁)).1 h₁
  have h₂' :
      Tendsto f (𝓝[S \ {p}] p) (𝓝 L₂) :=
    (metricLimitWithin_iff_tendsto (f := f) (S := S) (p := p) (L := L₂)).1 h₂
  have hmem : p ∈ closure (S \ {p}) :=
    (metricClusterPoint_iff_mem_closure_diff (p := p) (S := S)).1 hp
  have hnebot : NeBot (𝓝[S \ {p}] p) :=
    (mem_closure_iff_nhdsWithin_neBot (x := p) (s := S \ {p})).1 hmem
  exact tendsto_nhds_unique' (l := 𝓝[S \ {p}] p) (f := f) (a := L₁) (b := L₂) hnebot h₁' h₂'

/-- Lemma 7.5.17. A function on a subset of a metric space has limit `L` at a
cluster point `p` of the subset exactly when every sequence in the subset
avoiding `p` and converging to `p` has image sequence converging to `L`. -/
lemma metricLimitWithin_iff_tendsto_seq {S : Set X} {p : X} {f : X → Y} {L : Y}
    (hp : metricClusterPoint (X := X) p S) :
    metricLimitWithin (X := X) (Y := Y) f S p L ↔
      ∀ x : ℕ → X, (∀ n, x n ∈ S \ {p}) →
        Tendsto x atTop (𝓝 p) →
        Tendsto (fun n => f (x n)) atTop (𝓝 L) := by
  classical
  have _ : p ∈ closure (S \ {p}) :=
    (metricClusterPoint_iff_mem_closure_diff (p := p) (S := S)).1 hp
  constructor
  · intro hlim x hxmem hxT
    have hT : Tendsto f (𝓝[S \ {p}] p) (𝓝 L) :=
      (metricLimitWithin_iff_tendsto (f := f) (S := S) (p := p) (L := L)).1 hlim
    have hxT' : Tendsto x atTop (𝓝[S \ {p}] p) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within x hxT
        (Filter.Eventually.of_forall hxmem)
    exact hT.comp hxT'
  · intro hseq
    by_contra hlim
    unfold metricLimitWithin at hlim
    push_neg at hlim
    rcases hlim with ⟨ε, hε, hcounter⟩
    have hcounter' :
        ∀ n : ℕ, ∃ x, x ∈ S ∧ x ≠ p ∧ dist x p < 1 / (n + 1 : ℝ) ∧
          ε ≤ dist (f x) L := by
      intro n
      have hpos : 0 < (1 / (n + 1 : ℝ)) := by
        have : 0 < (n + 1 : ℝ) := by
          exact_mod_cast Nat.succ_pos n
        exact one_div_pos.mpr this
      rcases hcounter (1 / (n + 1 : ℝ)) hpos with ⟨x, hxS, hxne, hdist, hfar⟩
      exact ⟨x, hxS, hxne, hdist, hfar⟩
    choose x hx using hcounter'
    have hxmem : ∀ n, x n ∈ S \ {p} := by
      intro n
      rcases hx n with ⟨hxS, hxne, hdist, hfar⟩
      have : x n ∈ S ∧ x n ≠ p := ⟨hxS, hxne⟩
      simpa [Set.mem_diff, Set.mem_singleton_iff] using this
    have hxT : Tendsto x atTop (𝓝 p) := by
      refine (Metric.tendsto_atTop.2 ?_)
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
      refine ⟨N, ?_⟩
      intro n hn
      rcases hx n with ⟨hxS, hxne, hdist, hfar⟩
      have hle : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast (Nat.succ_le_succ hn)
      have hle_div : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast (Nat.succ_pos N)) hle
      have hlt_div : 1 / (n + 1 : ℝ) < δ := lt_of_le_of_lt hle_div hN
      exact lt_trans hdist hlt_div
    have hfxT := hseq x hxmem hxT
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hfxT) ε hε
    have hfar : ε ≤ dist (f (x N)) L := by
      rcases hx N with ⟨hxS, hxne, hdist, hfar⟩
      exact hfar
    have hlt : dist (f (x N)) L < ε := hN N (le_rfl)
    exact (not_lt_of_ge hfar) hlt

end

end Section05
end Chap07
