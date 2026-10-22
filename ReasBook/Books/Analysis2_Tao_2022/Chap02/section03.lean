/-
Authors: Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/Analysis2_Tao_2022/README.md (Contributors).
-/

import Mathlib

section Chap02
section Section03

/-- Theorem 2.5: [Continuous maps preserve compactness] If `f : X → Y` is continuous between metric
spaces and `K ⊆ X` is compact, then the image `f '' K` is compact. -/
theorem continuous_maps_preserve_compactness {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Continuous f) {K : Set X} (hK : IsCompact K) :
    IsCompact (f '' K) := by
  simpa using hK.image hf

/-- Helper for Proposition 2.15: a continuous real-valued function on a compact metric space is bounded in absolute value. -/
lemma helperForProposition_2_15_abs_bound {X : Type*} [MetricSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) : ∃ M : ℝ, ∀ x : X, |f x| ≤ M := by
  have hcompact : IsCompact (Set.univ : Set X) := isCompact_univ
  have hcont : ContinuousOn f (Set.univ : Set X) := hf.continuousOn
  rcases hcompact.exists_bound_of_continuousOn hcont with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x
  have hxmem : x ∈ (Set.univ : Set X) := by simp
  have hnorm : ‖f x‖ ≤ C := hC x hxmem
  simpa [Real.norm_eq_abs] using hnorm

/-- Helper for Proposition 2.15: existence of points attaining the maximum and minimum on a compact metric space. -/
lemma helperForProposition_2_15_exists_argmax_argmin {X : Type*} [MetricSpace X]
    [CompactSpace X] {f : X → ℝ} (hf : Continuous f) (hne : Nonempty X) :
    ∃ x_max x_min : X, (∀ x : X, f x ≤ f x_max) ∧ (∀ x : X, f x_min ≤ f x) := by
  letI : Nonempty X := hne
  have hcompact : IsCompact (Set.univ : Set X) := isCompact_univ
  have hcont : ContinuousOn f (Set.univ : Set X) := hf.continuousOn
  have hne_univ : (Set.univ : Set X).Nonempty := Set.univ_nonempty
  rcases hcompact.exists_isMaxOn hne_univ hcont with ⟨x_max, _, hx_max⟩
  rcases hcompact.exists_isMinOn hne_univ hcont with ⟨x_min, _, hx_min⟩
  refine ⟨x_max, x_min, ?_, ?_⟩
  · have hmax' : ∀ x : X, f x ≤ f x_max := by
      simpa [isMaxOn_univ_iff] using hx_max
    exact hmax'
  · have hmin' : ∀ x : X, f x_min ≤ f x := by
      simpa [isMinOn_univ_iff] using hx_min
    exact hmin'

/-- Proposition 2.15: [Maximum principle] Let `(X, d)` be a compact metric space and `f : X → ℝ`
continuous. (i) The function `f` is bounded on `X`. (ii) If `X ≠ ∅`, then there exist
`x_max, x_min : X` such that `f x_max` is a maximum and `f x_min` is a minimum of `f` on `X`. -/
theorem maximum_principle {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → ℝ}
    (hf : Continuous f) :
    (∃ M : ℝ, ∀ x : X, |f x| ≤ M) ∧
      (Nonempty X → ∃ x_max x_min : X, (∀ x : X, f x ≤ f x_max) ∧
        (∀ x : X, f x_min ≤ f x)) := by
  constructor
  · exact helperForProposition_2_15_abs_bound hf
  · intro hne
    exact helperForProposition_2_15_exists_argmax_argmin hf hne

/-- Definition 2.6: [Uniform continuity] Let `(X, d_X)` and `(Y, d_Y)` be metric spaces and
`f : X → Y`. The function `f` is uniformly continuous on `X` if for every `ε > 0` there exists
`δ > 0` such that for all `x, x' ∈ X`, `d_X x x' < δ → d_Y (f x) (f x') < ε`. -/
abbrev IsUniformlyContinuous {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  UniformContinuous f

/-- The predicate `IsUniformlyContinuous` coincides with mathlib's `UniformContinuous`. -/
lemma isUniformlyContinuous_iff_uniformContinuous {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) : IsUniformlyContinuous f ↔ UniformContinuous f := Iff.rfl

/-- Theorem 2.7: Let `(X, d_X)` and `(Y, d_Y)` be metric spaces and assume `X` is compact. For a
function `f : X → Y`, `f` is continuous on `X` if and only if `f` is uniformly continuous on `X`. -/
theorem continuous_iff_uniformlyContinuous_of_compact {X Y : Type*} [MetricSpace X]
    [MetricSpace Y] [CompactSpace X] {f : X → Y} :
    Continuous f ↔ IsUniformlyContinuous f := by
  constructor
  · intro hf
    have huc : UniformContinuous f :=
      CompactSpace.uniformContinuous_of_continuous (f := f) hf
    simpa [IsUniformlyContinuous] using huc
  · intro hf
    have huc : UniformContinuous f := by
      simpa [IsUniformlyContinuous] using hf
    exact huc.continuous

/-- Proposition 2.16: If `f : X → Y` and `g : Y → Z` are uniformly continuous between metric
spaces, then `g ∘ f : X → Z` is uniformly continuous. -/
theorem uniformlyContinuous_comp {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {f : X → Y} {g : Y → Z} (hf : IsUniformlyContinuous f)
    (hg : IsUniformlyContinuous g) : IsUniformlyContinuous (g ∘ f) := by
  dsimp [IsUniformlyContinuous] at hf hg ⊢
  exact hg.comp hf

/-- Helper for Proposition 2.17: Euclidean distance in `ℝ²` is bounded by the sum of coordinate distances. -/
lemma helperForProposition_2_17_dist_finTwo_pair_le_add (a b c d : ℝ) :
    dist (!₂[a,b] : EuclideanSpace ℝ (Fin 2)) !₂[c,d] ≤ dist a c + dist b d := by
  have hdist :
      dist (!₂[a,b] : EuclideanSpace ℝ (Fin 2)) !₂[c,d]
        = Real.sqrt (dist a c ^ 2 + dist b d ^ 2) := by
    simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, pow_two]
  calc
    dist (!₂[a,b] : EuclideanSpace ℝ (Fin 2)) !₂[c,d]
        = Real.sqrt (dist a c ^ 2 + dist b d ^ 2) := hdist
    _ ≤ dist a c + dist b d := by
        have hnonneg1 : 0 ≤ dist a c := dist_nonneg
        have hnonneg2 : 0 ≤ dist b d := dist_nonneg
        have hsum_nonneg : 0 ≤ dist a c + dist b d := add_nonneg hnonneg1 hnonneg2
        have hsq : dist a c ^ 2 + dist b d ^ 2 ≤ (dist a c + dist b d) ^ 2 := by
          nlinarith [hnonneg1, hnonneg2]
        exact (Real.sqrt_le_iff).2 ⟨hsum_nonneg, hsq⟩

/-- Helper for Proposition 2.17: coordinate-wise bound for paired maps. -/
lemma helperForProposition_2_17_dist_pair_le_add_coords {X : Type*} [MetricSpace X]
    {f g : X → ℝ} (x y : X) :
    dist (!₂[f x, g x] : EuclideanSpace ℝ (Fin 2)) !₂[f y, g y]
      ≤ dist (f x) (f y) + dist (g x) (g y) := by
  simpa using
    (helperForProposition_2_17_dist_finTwo_pair_le_add (f x) (g x) (f y) (g y))

/-- Proposition 2.17: Let `(X, d_X)` be a metric space, and let `f, g : X → ℝ` be uniformly
continuous. Equip `ℝ²` with the standard metric
`d((a, b), (c, d)) = √((a - c)^2 + (b - d)^2)`. Define `(f, g) : X → ℝ²` by
`(f, g)(x) = (f x, g x)`. Then `(f, g)` is uniformly continuous. -/
theorem uniformlyContinuous_pair {X : Type*} [MetricSpace X] {f g : X → ℝ}
    (hf : IsUniformlyContinuous f) (hg : IsUniformlyContinuous g) :
    IsUniformlyContinuous
      (fun x : X => !₂[f x, g x] : X → EuclideanSpace ℝ (Fin 2)) := by
  dsimp [IsUniformlyContinuous] at hf hg ⊢
  refine (Metric.uniformContinuous_iff).2 ?_
  intro ε hε
  have hf_eps := (Metric.uniformContinuous_iff).1 hf
  have hg_eps := (Metric.uniformContinuous_iff).1 hg
  have hε2 : 0 < ε / 2 := by
    linarith
  rcases hf_eps (ε / 2) hε2 with ⟨δf, hδf_pos, hδf⟩
  rcases hg_eps (ε / 2) hε2 with ⟨δg, hδg_pos, hδg⟩
  refine ⟨min δf δg, ?_, ?_⟩
  · exact (lt_min_iff).2 ⟨hδf_pos, hδg_pos⟩
  · intro x y hxy
    have hxy' : dist x y < δf ∧ dist x y < δg := (lt_min_iff).1 hxy
    have hfx : dist (f x) (f y) < ε / 2 := hδf hxy'.1
    have hgx : dist (g x) (g y) < ε / 2 := hδg hxy'.2
    have hdist_le :
        dist (!₂[f x, g x] : EuclideanSpace ℝ (Fin 2)) !₂[f y, g y]
          ≤ dist (f x) (f y) + dist (g x) (g y) :=
      helperForProposition_2_17_dist_pair_le_add_coords x y
    have hsum_lt : dist (f x) (f y) + dist (g x) (g y) < ε := by
      have hsum : dist (f x) (f y) + dist (g x) (g y) < ε / 2 + ε / 2 :=
        add_lt_add hfx hgx
      simpa [add_halves] using hsum
    exact lt_of_le_of_lt hdist_le hsum_lt

/-- The map `a(x,y)=x+y` on `ℝ²`, viewed as `EuclideanSpace ℝ (Fin 2)`. -/
def coordAdd : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0 + p 1

/-- The map `s(x,y)=x-y` on `ℝ²`, viewed as `EuclideanSpace ℝ (Fin 2)`. -/
def coordSub : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0 - p 1

/-- The map `m(x,y)=x*y` on `ℝ²`, viewed as `EuclideanSpace ℝ (Fin 2)`. -/
def coordMul : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0 * p 1

/-- Helper for Proposition 2.18: each coordinate distance is bounded by the Euclidean distance. -/
lemma helperForProposition_2_18_dist_coord0_coord1_le_dist
    (p q : EuclideanSpace ℝ (Fin 2)) :
    dist (p 0) (q 0) ≤ dist p q ∧ dist (p 1) (q 1) ≤ dist p q := by
  have hdist :
      dist p q = Real.sqrt (dist (p 0) (q 0) ^ 2 + dist (p 1) (q 1) ^ 2) := by
    simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, pow_two]
  have hcoord0 : dist (p 0) (q 0) ≤ dist p q := by
    have hsq :
        dist (p 0) (q 0) ^ 2 ≤ dist (p 0) (q 0) ^ 2 + dist (p 1) (q 1) ^ 2 := by
      nlinarith
    have hle :
        dist (p 0) (q 0) ≤
          Real.sqrt (dist (p 0) (q 0) ^ 2 + dist (p 1) (q 1) ^ 2) :=
      Real.le_sqrt_of_sq_le hsq
    simpa [hdist] using hle
  have hcoord1 : dist (p 1) (q 1) ≤ dist p q := by
    have hsq :
        dist (p 1) (q 1) ^ 2 ≤ dist (p 0) (q 0) ^ 2 + dist (p 1) (q 1) ^ 2 := by
      nlinarith
    have hle :
        dist (p 1) (q 1) ≤
          Real.sqrt (dist (p 0) (q 0) ^ 2 + dist (p 1) (q 1) ^ 2) :=
      Real.le_sqrt_of_sq_le hsq
    simpa [hdist] using hle
  exact ⟨hcoord0, hcoord1⟩

/-- Helper for Proposition 2.18: uniform continuity of `coordAdd`. -/
lemma helperForProposition_2_18_uniformlyContinuous_coordAdd :
    IsUniformlyContinuous coordAdd := by
  dsimp [IsUniformlyContinuous, coordAdd]
  refine (Metric.uniformContinuous_iff).2 ?_
  intro ε hε
  refine ⟨ε / 2, ?_, ?_⟩
  · linarith
  · intro p q hdist
    have hcoord := helperForProposition_2_18_dist_coord0_coord1_le_dist p q
    have hdist_le :
        dist (p 0 + p 1) (q 0 + q 1)
          ≤ dist (p 0) (q 0) + dist (p 1) (q 1) :=
      dist_add_add_le _ _ _ _
    have hsum_le :
        dist (p 0) (q 0) + dist (p 1) (q 1) ≤ dist p q + dist p q := by
      nlinarith [hcoord.1, hcoord.2]
    have hsum_lt : dist p q + dist p q < ε := by
      have hsum : dist p q + dist p q < ε / 2 + ε / 2 := add_lt_add hdist hdist
      simpa [add_halves] using hsum
    exact lt_of_le_of_lt (le_trans hdist_le hsum_le) hsum_lt

/-- Helper for Proposition 2.18: uniform continuity of `coordSub`. -/
lemma helperForProposition_2_18_uniformlyContinuous_coordSub :
    IsUniformlyContinuous coordSub := by
  dsimp [IsUniformlyContinuous, coordSub]
  refine (Metric.uniformContinuous_iff).2 ?_
  intro ε hε
  refine ⟨ε / 2, ?_, ?_⟩
  · linarith
  · intro p q hdist
    have hcoord := helperForProposition_2_18_dist_coord0_coord1_le_dist p q
    have hdist_le :
        dist (p 0 - p 1) (q 0 - q 1)
          ≤ dist (p 0) (q 0) + dist (p 1) (q 1) :=
      dist_sub_sub_le _ _ _ _
    have hsum_le :
        dist (p 0) (q 0) + dist (p 1) (q 1) ≤ dist p q + dist p q := by
      nlinarith [hcoord.1, hcoord.2]
    have hsum_lt : dist p q + dist p q < ε := by
      have hsum : dist p q + dist p q < ε / 2 + ε / 2 := add_lt_add hdist hdist
      simpa [add_halves] using hsum
    exact lt_of_le_of_lt (le_trans hdist_le hsum_le) hsum_lt

/-- Helper for Proposition 2.18: `coordMul` fails uniform continuity on `ℝ²`. -/
lemma helperForProposition_2_18_not_uniformlyContinuous_coordMul :
    ¬ IsUniformlyContinuous coordMul := by
  dsimp [IsUniformlyContinuous, coordMul]
  intro huc
  have huc' := (Metric.uniformContinuous_iff).1 huc
  have hε : 0 < (1 / 2 : ℝ) := by
    norm_num
  rcases huc' (1 / 2 : ℝ) hε with ⟨δ, hδpos, hδ⟩
  rcases exists_nat_one_div_lt hδpos with ⟨n, hn⟩
  let t : ℝ := (n : ℝ) + 1
  have htpos : 0 < t := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
      nlinarith
    simpa [t] using hpos
  have ht_ne : t ≠ 0 := ne_of_gt htpos
  let p : EuclideanSpace ℝ (Fin 2) := !₂[t, 0]
  let q : EuclideanSpace ℝ (Fin 2) := !₂[t, 1 / t]
  have hdist_pq : dist p q < δ := by
    have hdist_eq : dist p q = |t|⁻¹ := by
      simp [p, q, EuclideanSpace.dist_eq, Fin.sum_univ_two, pow_two]
    have hdist_eq' : dist p q = t⁻¹ := by
      simpa [abs_of_pos htpos] using hdist_eq
    have hlt : t⁻¹ < δ := by
      simpa [t] using hn
    simpa [hdist_eq'] using hlt
  have hdist_mul_lt : dist (coordMul p) (coordMul q) < (1 / 2 : ℝ) := hδ hdist_pq
  have hdist_mul_eq : dist (coordMul p) (coordMul q) = (1 : ℝ) := by
    simp [coordMul, p, q, ht_ne]
  have hlt : (1 : ℝ) < (1 / 2 : ℝ) := by
    simpa [hdist_mul_eq] using hdist_mul_lt
  linarith

/-- Proposition 2.18: On `ℝ²` with the Euclidean metric and `ℝ` with the usual metric, the maps
`a(x,y)=x+y` and `s(x,y)=x-y` are uniformly continuous, whereas `m(x,y)=x*y` is not uniformly
continuous. -/
lemma uniformlyContinuous_add_sub_not_mul :
    IsUniformlyContinuous coordAdd ∧ IsUniformlyContinuous coordSub ∧
      ¬ IsUniformlyContinuous coordMul := by
  refine And.intro ?_ ?_
  · exact helperForProposition_2_18_uniformlyContinuous_coordAdd
  · refine And.intro ?_ ?_
    · exact helperForProposition_2_18_uniformlyContinuous_coordSub
    · exact helperForProposition_2_18_not_uniformlyContinuous_coordMul

/-- Proposition 2.19: Let `(X, d)` be a metric space and let `f, g : X → ℝ` be uniformly
continuous. Then the functions `f + g` and `f - g` are uniformly continuous on `X`. -/
theorem uniformlyContinuous_add_sub {X : Type*} [MetricSpace X] {f g : X → ℝ}
    (hf : IsUniformlyContinuous f) (hg : IsUniformlyContinuous g) :
    IsUniformlyContinuous (f + g) ∧ IsUniformlyContinuous (f - g) := by
  have hpair :
      IsUniformlyContinuous
        (fun x : X => !₂[f x, g x] : X → EuclideanSpace ℝ (Fin 2)) :=
    uniformlyContinuous_pair hf hg
  have hadd :
      IsUniformlyContinuous
        (coordAdd ∘ (fun x : X => !₂[f x, g x] : X → EuclideanSpace ℝ (Fin 2))) :=
    uniformlyContinuous_comp hpair helperForProposition_2_18_uniformlyContinuous_coordAdd
  have hsub :
      IsUniformlyContinuous
        (coordSub ∘ (fun x : X => !₂[f x, g x] : X → EuclideanSpace ℝ (Fin 2))) :=
    uniformlyContinuous_comp hpair helperForProposition_2_18_uniformlyContinuous_coordSub
  refine And.intro ?_ ?_
  · simpa [Function.comp, coordAdd] using hadd
  · simpa [Function.comp, coordSub] using hsub

end Section03
end Chap02
