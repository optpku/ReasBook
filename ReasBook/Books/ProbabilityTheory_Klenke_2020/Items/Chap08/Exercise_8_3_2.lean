/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Notation

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω}

/-- Helper for Exercise 8.3.2: scaling both coordinates by the same nonnegative factor pulls that
factor out of the Hölder weighted geometric mean. -/
private lemma holderWeightedGeomScale {p q c x y : ℝ} (hpq : p.HolderConjugate q) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (c * x) ^ (1 / p) * (c * y) ^ (1 / q) = c * (x ^ (1 / p) * y ^ (1 / q)) := by
  have hmulx : (c * x) ^ (1 / p) = c ^ (1 / p) * x ^ (1 / p) := by
    simpa using (Real.mul_rpow hc hx (z := 1 / p))
  have hmuly : (c * y) ^ (1 / q) = c ^ (1 / q) * y ^ (1 / q) := by
    simpa using (Real.mul_rpow hc hy (z := 1 / q))
  have hmulc : c ^ (1 / p) * c ^ (1 / q) = c := by
    calc
      c ^ (1 / p) * c ^ (1 / q) = c ^ (1 / p + 1 / q) := by
        simpa using
          (Real.rpow_add_of_nonneg hc hpq.one_div_pos.le hpq.symm.one_div_pos.le).symm
      _ = c ^ (1 : ℝ) := by
        simpa [one_div] using congrArg (fun t : ℝ ↦ c ^ t) hpq.inv_add_inv_eq_one
      _ = c := by simp
  -- Rewrite the common scale through both `rpow` factors and recombine the exponents on `c`.
  calc
    (c * x) ^ (1 / p) * (c * y) ^ (1 / q)
        = (c ^ (1 / p) * x ^ (1 / p)) * (c ^ (1 / q) * y ^ (1 / q)) := by
            rw [hmulx, hmuly]
    _ = (c ^ (1 / p) * c ^ (1 / q)) * (x ^ (1 / p) * y ^ (1 / q)) := by ring
    _ = c * (x ^ (1 / p) * y ^ (1 / q)) := by rw [hmulc]

/-- Helper for Exercise 8.3.2: the two-point Hölder inequality yields the weighted geometric-mean
segment inequality on nonnegative scalars. -/
private lemma holderWeightedGeomTwoPoint {p q a b x₁ x₂ y₁ y₂ : ℝ}
    (hpq : p.HolderConjugate q) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    a * (x₁ ^ (1 / p) * y₁ ^ (1 / q)) + b * (x₂ ^ (1 / p) * y₂ ^ (1 / q)) ≤
      (a * x₁ + b * x₂) ^ (1 / p) * (a * y₁ + b * y₂) ^ (1 / q) := by
  let f : Fin 2 → ℝ
    | 0 => (a * x₁) ^ (1 / p)
    | 1 => (b * x₂) ^ (1 / p)
  let g : Fin 2 → ℝ
    | 0 => (a * y₁) ^ (1 / q)
    | 1 => (b * y₂) ^ (1 / q)
  have hf_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ f i := by
    intro i hi
    fin_cases i
    · simpa [f] using Real.rpow_nonneg (mul_nonneg ha hx₁) (1 / p)
    · simpa [f] using Real.rpow_nonneg (mul_nonneg hb hx₂) (1 / p)
  have hg_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ g i := by
    intro i hi
    fin_cases i
    · simpa [g] using Real.rpow_nonneg (mul_nonneg ha hy₁) (1 / q)
    · simpa [g] using Real.rpow_nonneg (mul_nonneg hb hy₂) (1 / q)
  have hf0 : ((a * x₁) ^ (1 / p)) ^ p = a * x₁ := by
    have hm : ((a * x₁) ^ (1 / p)) ^ p = (a * x₁) ^ ((1 / p) * p) := by
      simpa using (Real.rpow_mul (mul_nonneg ha hx₁) (1 / p) p).symm
    rw [hm]
    have hp_mul : (1 / p) * p = 1 := by field_simp [hpq.pos.ne']
    rw [hp_mul, Real.rpow_one]
  have hf1 : ((b * x₂) ^ (1 / p)) ^ p = b * x₂ := by
    have hm : ((b * x₂) ^ (1 / p)) ^ p = (b * x₂) ^ ((1 / p) * p) := by
      simpa using (Real.rpow_mul (mul_nonneg hb hx₂) (1 / p) p).symm
    rw [hm]
    have hp_mul : (1 / p) * p = 1 := by field_simp [hpq.pos.ne']
    rw [hp_mul, Real.rpow_one]
  have hg0 : ((a * y₁) ^ (1 / q)) ^ q = a * y₁ := by
    have hm : ((a * y₁) ^ (1 / q)) ^ q = (a * y₁) ^ ((1 / q) * q) := by
      simpa using (Real.rpow_mul (mul_nonneg ha hy₁) (1 / q) q).symm
    rw [hm]
    have hq_mul : (1 / q) * q = 1 := by field_simp [hpq.symm.pos.ne']
    rw [hq_mul, Real.rpow_one]
  have hg1 : ((b * y₂) ^ (1 / q)) ^ q = b * y₂ := by
    have hm : ((b * y₂) ^ (1 / q)) ^ q = (b * y₂) ^ ((1 / q) * q) := by
      simpa using (Real.rpow_mul (mul_nonneg hb hy₂) (1 / q) q).symm
    rw [hm]
    have hq_mul : (1 / q) * q = 1 := by field_simp [hpq.symm.pos.ne']
    rw [hq_mul, Real.rpow_one]
  have hsum_f : ∑ i ∈ (Finset.univ : Finset (Fin 2)), (f i) ^ p = a * x₁ + b * x₂ := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), (f i) ^ p
          = ((a * x₁) ^ (1 / p)) ^ p + ((b * x₂) ^ (1 / p)) ^ p := by
              simp [f]
      _ = a * x₁ + b * x₂ := by rw [hf0, hf1]
  have hsum_g : ∑ i ∈ (Finset.univ : Finset (Fin 2)), (g i) ^ q = a * y₁ + b * y₂ := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), (g i) ^ q
          = ((a * y₁) ^ (1 / q)) ^ q + ((b * y₂) ^ (1 / q)) ^ q := by
              simp [g]
      _ = a * y₁ + b * y₂ := by rw [hg0, hg1]
  have hleft :
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), f i * g i =
        a * (x₁ ^ (1 / p) * y₁ ^ (1 / q)) + b * (x₂ ^ (1 / p) * y₂ ^ (1 / q)) := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), f i * g i
          = (a * x₁) ^ (1 / p) * (a * y₁) ^ (1 / q) +
              (b * x₂) ^ (1 / p) * (b * y₂) ^ (1 / q) := by
                simp [f, g]
      _ = a * (x₁ ^ (1 / p) * y₁ ^ (1 / q)) + b * (x₂ ^ (1 / p) * y₂ ^ (1 / q)) := by
            rw [holderWeightedGeomScale hpq ha hx₁ hy₁, holderWeightedGeomScale hpq hb hx₂ hy₂]
  have hHolder :=
    Real.inner_le_Lp_mul_Lq_of_nonneg (s := (Finset.univ : Finset (Fin 2))) hpq hf_nonneg
      hg_nonneg
  -- Specialize finite Hölder to the two weighted points and normalize the two sums.
  calc
    a * (x₁ ^ (1 / p) * y₁ ^ (1 / q)) + b * (x₂ ^ (1 / p) * y₂ ^ (1 / q))
        = ∑ i ∈ (Finset.univ : Finset (Fin 2)), f i * g i := by rw [hleft.symm]
    _ ≤ (∑ i ∈ (Finset.univ : Finset (Fin 2)), (f i) ^ p) ^ (1 / p) *
          (∑ i ∈ (Finset.univ : Finset (Fin 2)), (g i) ^ q) ^ (1 / q) := hHolder
    _ = (a * x₁ + b * x₂) ^ (1 / p) * (a * y₁ + b * y₂) ^ (1 / q) := by
          rw [hsum_f, hsum_g]

/-- Helper for Exercise 8.3.2: the scalar two-point Hölder inequality gives the segment inequality
for the weighted geometric mean on the nonnegative quadrant. -/
private lemma holderWeightedGeomSegmentLe {p q : ℝ} (hpq : p.HolderConjugate q)
    {x y : ℝ × ℝ} (hx : x ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
    (hy : y ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * (x.1 ^ (1 / p) * x.2 ^ (1 / q)) + b * (y.1 ^ (1 / p) * y.2 ^ (1 / q)) ≤
      (a • x + b • y).1 ^ (1 / p) * (a • x + b • y).2 ^ (1 / q) := by
  have hx1 : 0 ≤ x.1 := by simpa [Set.mem_Ici] using hx.1
  have hx2 : 0 ≤ x.2 := by simpa [Set.mem_Ici] using hx.2
  have hy1 : 0 ≤ y.1 := by simpa [Set.mem_Ici] using hy.1
  have hy2 : 0 ≤ y.2 := by simpa [Set.mem_Ici] using hy.2
  -- Rewrite the segment coordinates as weighted sums and apply the scalar inequality once.
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
    using holderWeightedGeomTwoPoint hpq ha hb hx1 hy1 hx2 hy2

/-- Helper for Exercise 8.3.2: the weighted geometric mean associated with Hölder-conjugate
exponents is concave on the nonnegative quadrant. -/
lemma holderWeightedGeom_concaveOn {p q : ℝ} (hpq : p.HolderConjugate q) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
      (fun z : ℝ × ℝ ↦ z.1 ^ (1 / p) * z.2 ^ (1 / q)) := by
  -- Route correction: prove concavity from the two-point Hölder inequality instead of a direct
  -- `rpow` normalization inside the final `ConcaveOn` goal.
  rw [concaveOn_iff_forall_pos]
  constructor
  · simpa using (convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ))
  · intro x hx y hy a b ha hb hab
    -- Positive segment weights place us in the exact scalar Hölder inequality proved above.
    simpa using holderWeightedGeomSegmentLe hpq hx hy ha.le hb.le

/-- Helper for Exercise 8.3.2: Hölder-conjugate exponents recover `|x|` and `|y|` from their
`p`- and `q`-moments, so the weighted geometric mean equals `|x * y|`. -/
private lemma holderWeightedGeom_eq_abs_mul {p q x y : ℝ} (hpq : p.HolderConjugate q) :
    (|x| ^ p) ^ (1 / p) * (|y| ^ q) ^ (1 / q) = |x * y| := by
  have hp_pos : 0 < p := hpq.pos
  have hq_pos : 0 < q := hpq.symm.pos
  rw [abs_mul]
  rw [← Real.rpow_mul (abs_nonneg x), mul_one_div_cancel hp_pos.ne', Real.rpow_one]
  rw [← Real.rpow_mul (abs_nonneg y), mul_one_div_cancel hq_pos.ne', Real.rpow_one]

/-- Helper for Exercise 8.3.2: the Hölder weighted geometric mean is upper semicontinuous on the
nonnegative quadrant because each coordinate `rpow` is continuous there. -/
private lemma holderWeightedGeom_upperSemicontinuousOn {p q : ℝ} (hpq : p.HolderConjugate q) :
    UpperSemicontinuousOn
      (fun z : ℝ × ℝ ↦ z.1 ^ (1 / p) * z.2 ^ (1 / q))
      (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
  have hcont₁ : Continuous fun z : ℝ × ℝ ↦ z.1 ^ (1 / p) :=
    (Real.continuous_rpow_const hpq.one_div_pos.le).comp continuous_fst
  have hcont₂ : Continuous fun z : ℝ × ℝ ↦ z.2 ^ (1 / q) :=
    (Real.continuous_rpow_const hpq.symm.one_div_pos.le).comp continuous_snd
  have hcont :
      Continuous fun z : ℝ × ℝ ↦ z.1 ^ (1 / p) * z.2 ^ (1 / q) := by
    exact hcont₁.mul hcont₂
  exact hcont.continuousOn.upperSemicontinuousOn

/-- Helper for Exercise 8.3.2: under the measurable-sub-σ-algebra and σ-finite trim hypotheses,
conditional Hölder follows from conditional Jensen applied to the pair of conditional moments. -/
private lemma condExp_abs_mul_ae_le_of_holderConjugate_of_le_of_sigmaFinite
    {ℱ : MeasurableSpace Ω} {p q : ℝ} (hpq : p.HolderConjugate q) (hℱ : ℱ ≤ mΩ)
    [SigmaFinite (P.trim hℱ)] {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal q) P) :
    P[fun ω ↦ |X ω * Y ω| | ℱ] ≤ᵐ[P]
      P[fun ω ↦ |X ω| ^ p | ℱ] ^ (1 / p) * P[fun ω ↦ |Y ω| ^ q | ℱ] ^ (1 / q) := by
  have hp_pos : 0 < p := hpq.pos
  have hq_pos : 0 < q := hpq.symm.pos
  let s : Set (ℝ × ℝ) := Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)
  let φ : ℝ × ℝ → ℝ := fun z ↦ z.1 ^ (1 / p) * z.2 ^ (1 / q)
  let F : Ω → ℝ × ℝ := fun ω ↦ (|X ω| ^ p, |Y ω| ^ q)
  -- Package the `p`- and `q`-moments into a pair-valued integrable function.
  have hXp : Integrable (fun ω ↦ |X ω| ^ p) P := by
    simpa [Real.norm_eq_abs, hp_pos.le] using
      hX.integrable_norm_rpow (by simpa [hpq.pos.ne']) (by simp)
  have hYq : Integrable (fun ω ↦ |Y ω| ^ q) P := by
    simpa [Real.norm_eq_abs, hq_pos.le] using
      hY.integrable_norm_rpow (by simpa [hpq.symm.pos.ne']) (by simp)
  have hF_int : Integrable F P :=
    hXp.prodMk hYq
  have hF_mem : ∀ᵐ ω ∂P, F ω ∈ s := by
    exact Filter.Eventually.of_forall fun ω ↦
      ⟨Real.rpow_nonneg (abs_nonneg _) _, Real.rpow_nonneg (abs_nonneg _) _⟩
  letI : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := hpq.ennrealOfReal
  have hXY_int : Integrable (X * Y) P :=
    MemLp.integrable_mul hX hY
  have hφF_ae :
      φ ∘ F =ᵐ[P] fun ω ↦ |X ω * Y ω| := by
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [Function.comp, φ, F] using
        holderWeightedGeom_eq_abs_mul (hpq := hpq) (x := X ω) (y := Y ω)
  have hφF_int : Integrable (φ ∘ F) P := by
    -- Reuse the pointwise identification with `|X * Y|` for integrability and for the final
    -- conditional expectation rewrite.
    exact hXY_int.norm.congr hφF_ae.symm
  have hφ_concave : ConcaveOn ℝ s φ :=
    holderWeightedGeom_concaveOn hpq
  have hφ_upper : UpperSemicontinuousOn φ s := by
    simpa [φ, s] using holderWeightedGeom_upperSemicontinuousOn hpq
  -- Apply conditional Jensen to the pair-valued conditional expectation.
  have hJensen : P[φ ∘ F | ℱ] ≤ᵐ[P] φ ∘ P[F | ℱ] :=
    hφ_concave.condExp_map_le hℱ hφ_upper hF_mem (isClosed_Ici.prod isClosed_Ici) hF_int
      hφF_int
  have hfst :
      (fun ω ↦ (P[F | ℱ] ω).1) =ᵐ[P] P[fun ω ↦ |X ω| ^ p | ℱ] := by
    simpa [F] using
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_condExp_comm (μ := P) (m := ℱ) hF_int
  have hsnd :
      (fun ω ↦ (P[F | ℱ] ω).2) =ᵐ[P] P[fun ω ↦ |Y ω| ^ q | ℱ] := by
    simpa [F] using
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_condExp_comm (μ := P) (m := ℱ) hF_int
  have hleft :
      P[φ ∘ F | ℱ] =ᵐ[P] P[fun ω ↦ |X ω * Y ω| | ℱ] := by
    exact condExp_congr_ae hφF_ae
  -- The coordinate projections identify the Jensen bound with the two scalar conditional moments.
  exact hleft.symm.trans_le <| by
    filter_upwards [hJensen, hfst, hsnd] with ω hω hfstω hsndω
    simpa [φ, hfstω, hsndω] using hω

-- Proof sketch: package the conditional `p`- and `q`-moments into a pair-valued function,
-- prove concavity of the weighted geometric mean on the nonnegative quadrant, and apply
-- conditional Jensen. The side case `¬ ℱ ≤ mΩ` is automatic from `condExp_of_not_le`.
/-- Exercise 8.3.2: conditional Hölder's inequality. If `p` and `q` are Hölder-conjugate and
`X ∈ ℒ^p(P)`, `Y ∈ ℒ^q(P)`, then the conditional expectation of `|XY|` is bounded almost surely
by the product of the conditional `L^p` and `L^q` moments. This is the canonical
`Real.HolderConjugate` formulation of the textbook assumptions `p, q ∈ (1, ∞)` and
`1 / p + 1 / q = 1`. -/
theorem condExp_abs_mul_ae_le_of_holderConjugate {ℱ : MeasurableSpace Ω} {p q : ℝ}
    (hpq : p.HolderConjugate q) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal q) P) :
    P[fun ω ↦ |X ω * Y ω| | ℱ] ≤ᵐ[P]
      P[fun ω ↦ |X ω| ^ p | ℱ] ^ (1 / p) * P[fun ω ↦ |Y ω| ^ q | ℱ] ^ (1 / q) := by
  by_cases hℱ : ℱ ≤ mΩ
  · by_cases hσ : SigmaFinite (P.trim hℱ)
    · letI : SigmaFinite (P.trim hℱ) := hσ
      exact
        @condExp_abs_mul_ae_le_of_holderConjugate_of_le_of_sigmaFinite
          Ω mΩ P ℱ p q hpq hℱ (by infer_instance) X Y hX hY
    · exact Filter.Eventually.of_forall fun _ ↦ by
        have hp_pos : 0 < p := hpq.pos
        have hq_pos : 0 < q := hpq.symm.pos
        suffices 0 ≤ (0 : ℝ) ^ (1 / p) * 0 ^ (1 / q) by
          simpa [condExp_of_not_sigmaFinite hℱ hσ] using this
        positivity
  · exact Filter.Eventually.of_forall fun _ ↦ by
      have hp_pos : 0 < p := hpq.pos
      have hq_pos : 0 < q := hpq.symm.pos
      suffices 0 ≤ (0 : ℝ) ^ (1 / p) * 0 ^ (1 / q) by
        simpa [condExp_of_not_le hℱ] using this
      positivity
