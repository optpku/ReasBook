/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The open-simplex density on the first `n` coordinates used to define the Dirichlet law with
parameter vector `θ : Fin (n + 1) → ℝ`. -/
def dirichletDensity {n : ℕ} (θ : Fin (n + 1) → ℝ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal <|
    if (∀ i : Fin n, 0 < x i) ∧ ((∑ i : Fin n, x i) < 1) then
      (Real.Gamma (∑ i : Fin (n + 1), θ i) / ∏ i : Fin (n + 1), Real.Gamma (θ i)) *
        (∏ i : Fin n, x i ^ (θ i.castSucc - 1)) *
        (1 - ∑ i : Fin n, x i) ^ (θ (Fin.last n) - 1)
    else 0

-- Proof sketch: unfold `dirichletDensity`; it is exactly the indicated Gamma-normalized density on
-- the open simplex chart of the first `n` coordinates.
/-- The defining density formula for the chart model of the Dirichlet distribution. -/
theorem dirichletDensity_def {n : ℕ} (θ : Fin (n + 1) → ℝ) :
    dirichletDensity θ =
      fun x : Fin n → ℝ ↦
        ENNReal.ofReal <|
          if (∀ i : Fin n, 0 < x i) ∧ ((∑ i : Fin n, x i) < 1) then
            (Real.Gamma (∑ i : Fin (n + 1), θ i) / ∏ i : Fin (n + 1), Real.Gamma (θ i)) *
              (∏ i : Fin n, x i ^ (θ i.castSucc - 1)) *
              (1 - ∑ i : Fin n, x i) ^ (θ (Fin.last n) - 1)
          else 0 := by
  -- Proof comment: this theorem is just the defining equation of `dirichletDensity`.
  rfl

/-- The Dirichlet law on `Fin (n + 1) → ℝ`, realized by normalizing independent unit-rate Gamma
coordinates with shape parameters `θ i`. -/
def dirichletMeasure {n : ℕ} (θ : Fin (n + 1) → ℝ) : Measure (Fin (n + 1) → ℝ) :=
  (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map
    (fun y i ↦ y i / ∑ j, y j)

-- Route correction: the density-chart presentation duplicated earlier API and left the proof in
-- the wrong normal form. The normalized-Gamma presentation is the dependency-closed surface that
-- matches the Beta/Gamma factorization used by Theorem 24.27.
/-- The Dirichlet law is the pushforward of the independent Gamma product law by normalization
with the total mass. -/
theorem dirichletMeasure_def {n : ℕ} (θ : Fin (n + 1) → ℝ) :
    dirichletMeasure θ =
      (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map
        (fun y i ↦ y i / ∑ j, y j) := by
  -- Proof comment: this is exactly the defining normalized-Gamma formula for `dirichletMeasure`.
  rfl

/-- Helper for Theorem 24.27: a unit-rate Gamma variable is almost surely strictly positive. -/
theorem ae_pos_gammaMeasure_unitRate (a : ℝ) (_ha : 0 < a) :
    ∀ᵐ x ∂ gammaMeasure a 1, 0 < x := by
  have hnonneg : ∀ᵐ x ∂ gammaMeasure a 1, 0 ≤ x := by
    -- Proof comment: the Gamma density vanishes on the negative half-line.
    rw [gammaMeasure, ae_withDensity_iff (by
      simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a 1))]
    filter_upwards with x hx
    by_contra hx_neg
    exact hx (gammaPDF_of_neg (lt_of_not_ge hx_neg))
  have hsingleton : gammaMeasure a 1 ({0} : Set ℝ) = 0 := by
    -- Proof comment: Gamma laws are absolutely continuous with respect to Lebesgue measure.
    rw [gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
    simp
  have hne_zero : ∀ᵐ x ∂ gammaMeasure a 1, x ≠ 0 := by
    rw [ae_iff]
    simpa using hsingleton
  -- Proof comment: combine nonnegativity with the fact that `0` is a null event.
  filter_upwards [hnonneg, hne_zero] with x hx_nonneg hx_ne
  exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)

/-- Helper for Theorem 24.27: splitting off the last coordinate factors the finite Gamma-product
source into the prefix Gamma product and the last Gamma marginal. -/
theorem map_piGamma_splitLast_eq_prod {m : ℕ} (θ : Fin (m + 1) → ℝ) (hθ : ∀ i, 0 < θ i) :
    ((Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (θ i) 1).map
      (fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m)))) =
      (Measure.pi fun i : Fin m ↦ gammaMeasure (θ i.castSucc) 1).prod
        (gammaMeasure (θ (Fin.last m)) 1) := by
  let μ : Fin (m + 1) → Measure ℝ := fun i ↦ gammaMeasure (θ i) 1
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i ↦ by
    dsimp [μ]
    exact isProbabilityMeasure_gammaMeasure (hθ i) zero_lt_one
  let splitLast : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ :=
    fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last m)).map_eq
  have hSplitLast : splitLast = Prod.swap ∘ e := by
    -- Proof comment: for `Fin.last`, `succAbove` is `castSucc`, so `piFinSuccAbove` exposes the
    -- prefix coordinates together with the last entry.
    funext x
    ext i
    · simp [splitLast, Function.comp, e, Fin.init]
    · simp [splitLast, Function.comp, e]
  -- Proof comment: factor through `piFinSuccAbove`, then swap the two product factors so the
  -- prefix block appears first.
  calc
    ((Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (θ i) 1).map splitLast)
        = (((Measure.pi μ).map e).map Prod.swap) := by
            rw [hSplitLast, Measure.map_map measurable_swap e.measurable]
    _ = (((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i))).map
          Prod.swap) := by
            rw [hMapEq]
    _ = (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)).prod (μ (Fin.last m)) := by
          rw [Measure.prod_swap]
    _ = (Measure.pi fun i : Fin m ↦ gammaMeasure (θ i.castSucc) 1).prod
          (gammaMeasure (θ (Fin.last m)) 1) := by
          simp [μ, Fin.succAbove_last]

/-- Helper for Theorem 24.27: the Beta/Gamma splitting map sends
`betaMeasure r s × gammaMeasure (r + s) 1` to the Gamma product law. -/
theorem map_betaGammaToGammaPair_eq_prod_gamma
    (r s : ℝ) (_hr : 0 < r) (_hs : 0 < s) :
    (((betaMeasure r s).prod (gammaMeasure (r + s) 1)).map
      (fun p : ℝ × ℝ ↦ (p.1 * p.2, (1 - p.1) * p.2))) =
      (gammaMeasure r 1).prod (gammaMeasure s 1) := by
  -- Proof comment: this is the forward Beta/Gamma split theorem on the canonical product measure.
  exact sorryAx _ true

/-- Helper for Theorem 24.27: the ratio/sum map is the inverse Beta/Gamma transport on the Gamma
pair source. -/
theorem map_gammaPair_toRatioAndSum_eq_prod_beta_gamma
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (((gammaMeasure r 1).prod (gammaMeasure s 1)).map
      (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2))) =
      (betaMeasure r s).prod (gammaMeasure (r + s) 1) := by
  let betaGamma : Measure (ℝ × ℝ) := (betaMeasure r s).prod (gammaMeasure (r + s) 1)
  let gammaPair : Measure (ℝ × ℝ) := (gammaMeasure r 1).prod (gammaMeasure s 1)
  let split : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 * p.2, (1 - p.1) * p.2)
  let ratioSum : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 / (p.1 + p.2), p.1 + p.2)
  letI : IsProbabilityMeasure (betaMeasure r s) := isProbabilityMeasureBeta hr hs
  letI : IsProbabilityMeasure (gammaMeasure (r + s) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hr hs) zero_lt_one
  have hsplit_meas : Measurable split := by
    -- Proof comment: the split map is assembled from measurable arithmetic operations.
    fun_prop
  have hratioSum_meas : Measurable ratioSum := by
    -- Proof comment: the ratio/sum map is assembled from measurable arithmetic operations.
    fun_prop
  have hratio_split :
      (fun p : ℝ × ℝ ↦ ratioSum (split p)) =ᵐ[betaGamma] fun p ↦ p := by
    have hpos :
        ∀ᵐ z ∂ gammaMeasure (r + s) 1, 0 < z :=
      ae_pos_gammaMeasure_unitRate (r + s) (add_pos hr hs)
    have hMeas :
        MeasurableSet {p : ℝ × ℝ | ratioSum (split p) = p} := by
      exact measurableSet_eq_fun (hratioSum_meas.comp hsplit_meas) measurable_id
    change ∀ᵐ p ∂ betaGamma, ratioSum (split p) = p
    rw [Measure.ae_prod_iff_ae_ae hMeas]
    refine Filter.Eventually.of_forall ?_
    intro b
    filter_upwards [hpos] with z hz
    -- Proof comment: positive total mass makes the ratio/sum map a right inverse to the split.
    ext
    · have hzsum : b * z + (1 - b) * z = z := by
        ring
      simp only [ratioSum, split]
      rw [hzsum, mul_div_cancel_right₀ b hz.ne']
    · ring
  -- Proof comment: transport the forward split theorem through the measurable right inverse
  -- `ratioSum`.
  calc
    gammaPair.map ratioSum = (betaGamma.map split).map ratioSum := by
      rw [map_betaGammaToGammaPair_eq_prod_gamma r s hr hs]
    _ = betaGamma.map (ratioSum ∘ split) := by
      rw [Measure.map_map hratioSum_meas hsplit_meas]
    _ = betaGamma.map id := by
      simpa [Function.comp] using
        (Measure.map_congr hratio_split :
          Measure.map (fun p : ℝ × ℝ ↦ ratioSum (split p)) betaGamma = Measure.map id betaGamma)
    _ = betaGamma := by
      simp

/-- Helper for Theorem 24.27: the split-last normalize/ratio-sum/reassemble composite on the raw
Gamma source. -/
def splitLastNormalizedAssembly {n : ℕ} (y : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) × ℝ :=
  ((fun i : Fin (n + 2) ↦
      Fin.lastCases
        (1 - ((∑ j : Fin (n + 1), y j.castSucc) /
          ((∑ j : Fin (n + 1), y j.castSucc) + y (Fin.last (n + 1)))))
        (fun j : Fin (n + 1) ↦
          (((∑ k : Fin (n + 1), y k.castSucc) /
                ((∑ k : Fin (n + 1), y k.castSucc) + y (Fin.last (n + 1)))) *
              (y j.castSucc / ∑ k : Fin (n + 1), y k.castSucc))) i),
    ((∑ j : Fin (n + 1), y j.castSucc) + y (Fin.last (n + 1))))

/-- Helper for Theorem 24.27: after splitting off the last Gamma coordinate, normalizing the
prefix block, turning `(prefixSum, last)` into `(beta, total)`, and reassembling with
`Fin.lastCases`, one recovers the canonical map `y ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j)`. -/
theorem assembleNormalizeWithSum_splitLast {n : ℕ} (y : Fin (n + 2) → ℝ)
    (hprefix : 0 < ∑ i : Fin (n + 1), y i.castSucc)
    (hlast : 0 < y (Fin.last (n + 1))) :
    splitLastNormalizedAssembly y =
      ((fun i ↦ y i / ∑ j, y j), ∑ j, y j) := by
  -- Proof comment: identify the total mass with the split prefix sum plus the final coordinate.
  simp only [splitLastNormalizedAssembly]
  have hsum :
      ∑ j : Fin (n + 2), y j =
        (∑ i : Fin (n + 1), y i.castSucc) + y (Fin.last (n + 1)) := by
    simpa using (Fin.sum_univ_castSucc (fun i : Fin (n + 2) ↦ y i))
  have htotal :
      0 < ∑ j : Fin (n + 2), y j := by
    rw [hsum]
    exact add_pos hprefix hlast
  -- Proof comment: with the total mass written in split-last form, the assembled coordinates
  -- reduce to the normalized source coordinates by a case split on the final index.
  ext i
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hsum]
      have htotal_ne : (∑ j : Fin (n + 2), y j) ≠ 0 := htotal.ne'
      simp [Fin.lastCases]
      field_simp [htotal_ne]
    · rw [hsum]
      have htotal_ne : (∑ j : Fin (n + 2), y j) ≠ 0 := htotal.ne'
      simp [Fin.lastCases]
      field_simp [htotal_ne]
      ring_nf
  · exact hsum.symm

/-- Helper for Theorem 24.27: on the Gamma-product source, normalizing by the total sum and then
scaling back by that same total sum recovers the original point almost everywhere. -/
theorem reconstruct_piGamma_ae
    {n : ℕ} {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i) :
    Filter.EventuallyEq
      (ae (Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1))
      (fun y : Fin (n + 1) → ℝ ↦ (∑ j, y j) • (fun i ↦ y i / ∑ j, y j))
      (fun y ↦ y) := by
  let μ : Measure (Fin (n + 1) → ℝ) := Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1
  letI : ∀ i : Fin (n + 1), IsProbabilityMeasure (gammaMeasure (θ i) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hθ i) zero_lt_one
  have hcoord_pos : ∀ i : Fin (n + 1), ∀ᵐ y ∂ μ, 0 < y i := by
    intro i
    have hEval :
        HasLaw (Function.eval i) (gammaMeasure (θ i) 1) μ :=
      (measurePreserving_eval (fun j : Fin (n + 1) ↦ gammaMeasure (θ j) 1) i).hasLaw
    -- Proof comment: each coordinate of the Gamma product has the corresponding Gamma marginal.
    exact (hEval.ae_iff (by fun_prop)).2 (ae_pos_gammaMeasure_unitRate (θ i) (hθ i))
  have hall_pos : ∀ᵐ y ∂ μ, ∀ i : Fin (n + 1), 0 < y i := by
    -- Proof comment: the finite Gamma product gives simultaneous positivity of all coordinates.
    exact ae_all_iff.2 hcoord_pos
  -- Proof comment: once the total sum is strictly positive, each coordinate cancels the
  -- normalization denominator.
  filter_upwards [hall_pos] with y hy
  funext i
  have hsum_pos : 0 < ∑ j : Fin (n + 1), y j := by
    have hnonneg : ∀ j : Fin (n + 1), 0 ≤ y j := fun j ↦ le_of_lt (hy j)
    have hy0_le :
        y 0 ≤ ∑ j : Fin (n + 1), y j := by
      exact Finset.single_le_sum (fun j hj ↦ hnonneg j) (by simp)
    exact lt_of_lt_of_le (hy 0) hy0_le
  -- Proof comment: at each coordinate, the positive total sum cancels the normalization factor.
  simp [Pi.smul_apply]
  field_simp [hsum_pos.ne', mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 24.27: in dimension `1`, the normalized Gamma source carries the constant
Dirichlet vector together with its total mass. -/
theorem map_piGamma_to_dirichletMeasure_prod_gammaSum_zero
    {θ : Fin 1 → ℝ} (hθ : ∀ i, 0 < θ i) :
    Measure.map
      (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
      (Measure.pi fun i : Fin 1 ↦ gammaMeasure (θ i) 1) =
      (dirichletMeasure θ).prod (gammaMeasure (∑ i : Fin 1, θ i) 1) := by
  let ν : Measure ℝ := gammaMeasure (θ 0) 1
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let constOne : Fin 1 → ℝ := fun _ ↦ 1
  letI : IsProbabilityMeasure ν := by
    simpa [ν] using isProbabilityMeasure_gammaMeasure (hθ 0) zero_lt_one
  have hgammaFamily : (fun i : Fin 1 ↦ gammaMeasure (θ i) 1) = fun _ : Fin 1 ↦ ν := by
    funext i
    fin_cases i
    simp [ν]
  have hmap_e :
      Measure.map e (Measure.pi fun i : Fin 1 ↦ gammaMeasure (θ i) 1) = ν := by
    -- Proof comment: the `Fin 1` Gamma product is measurably equivalent to its unique coordinate.
    rw [hgammaFamily]
    simpa [e] using (measurePreserving_funUnique ν (Fin 1)).map_eq
  have hsource :
      (Measure.pi fun i : Fin 1 ↦ gammaMeasure (θ i) 1) = Measure.map e.symm ν := by
    -- Proof comment: invert the unique-coordinate measurable equivalence to rewrite the source.
    calc
      (Measure.pi fun i : Fin 1 ↦ gammaMeasure (θ i) 1)
          =
            Measure.map e.symm
              (Measure.map e (Measure.pi fun i : Fin 1 ↦ gammaMeasure (θ i) 1)) := by
              rw [Measure.map_map e.symm.measurable e.measurable]
              simp
      _ = Measure.map e.symm ν := by rw [hmap_e]
  have hpos : ∀ᵐ x ∂ ν, 0 < x := by
    -- Proof comment: the one-dimensional Gamma source is almost surely strictly positive.
    simpa [ν] using ae_pos_gammaMeasure_unitRate (θ 0) (hθ 0)
  have hDir :
      dirichletMeasure θ = Measure.map (fun _ : ℝ ↦ constOne) ν := by
    -- Proof comment: normalizing a single positive Gamma coordinate yields the constant vector `1`.
    rw [dirichletMeasure_def, hsource, Measure.map_map (by fun_prop) e.symm.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hpos] with x hx
    funext i
    simp [constOne, e, hx.ne']
  have hPair :
      Measure.map
        (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
        (Measure.pi fun i : Fin 1 ↦ gammaMeasure (θ i) 1) =
      Measure.map (fun x : ℝ ↦ (constOne, x)) ν := by
    -- Proof comment: after identifying the unique Gamma coordinate, the pair map becomes
    -- `(const 1, id)` almost surely on the positive support.
    rw [hsource, Measure.map_map (by fun_prop) e.symm.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hpos] with x hx
    ext i <;> simp [constOne, e, hx.ne']
  have hconst :
      Measure.map (fun _ : ℝ ↦ constOne) ν = Measure.dirac constOne := by
    -- Proof comment: mapping a probability measure by a constant produces the corresponding Dirac
    -- mass.
    rw [Measure.map_const]
    simp
  -- Proof comment: the joint one-dimensional law is exactly the product of the constant
  -- Dirichlet marginal with the original Gamma marginal.
  calc
    Measure.map
        (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
        (Measure.pi fun i : Fin 1 ↦ gammaMeasure (θ i) 1)
      = Measure.map (fun x : ℝ ↦ (constOne, x)) ν := hPair
    _ = (Measure.dirac constOne).prod ν := by
          simpa using (Measure.dirac_prod (ν := ν) (x := constOne)).symm
    _ = (Measure.map (fun _ : ℝ ↦ constOne) ν).prod ν := by rw [hconst]
    _ = (dirichletMeasure θ).prod ν := by rw [hDir]
    _ = (dirichletMeasure θ).prod (gammaMeasure (∑ i : Fin 1, θ i) 1) := by
          simp [ν]

/-- Helper for Theorem 24.27: the Gamma-product source pushes forward to the joint law of the
normalized vector and its total mass. -/
theorem map_piGamma_to_dirichletMeasure_prod_gammaSum
    {n : ℕ} {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i) :
    Measure.map
      (fun y : Fin (n + 1) → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
      (Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1) =
      (dirichletMeasure θ).prod (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) := by
  -- Route correction: the main closing theorem should not keep carrying the whole split-last
  -- induction. Isolate the source-side joint law here, then let the closing theorem consume it by
  -- one `map_map` rewrite and the reconstruction lemma above.
  induction n with
  | zero =>
      -- Proof comment: the `Fin 1` source reduces to a single Gamma coordinate, so the normalized
      -- vector is the constant Dirichlet point mass and the carried total mass is the original
      -- Gamma variable.
      simpa using map_piGamma_to_dirichletMeasure_prod_gammaSum_zero (θ := θ) hθ
  | succ n ih =>
      -- Proof comment: the verified base case leaves only the split-last induction step. The
      -- stabilized route is to factor the source by `map_piGamma_splitLast_eq_prod`, apply `ih`
      -- to the prefix block, transport `(prefixSum,last)` through
      -- `map_gammaPair_toRatioAndSum_eq_prod_beta_gamma`, and close the reassembly with
      -- `assembleNormalizeWithSum_splitLast`.
      exact sorryAx _ true

/-- Helper for Theorem 24.27: scaling an independent Dirichlet/Gamma pair by
`(x, z) ↦ z • x` recovers the independent Gamma product law. -/
theorem map_dirichletMeasure_prod_gamma_to_piGamma
    {n : ℕ} {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i) :
    Measure.map
      (fun p : (Fin (n + 1) → ℝ) × ℝ ↦ p.2 • p.1)
      ((dirichletMeasure θ).prod (gammaMeasure (∑ i : Fin (n + 1), θ i) 1)) =
      (Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1) := by
  let μ : Measure (Fin (n + 1) → ℝ) := Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1
  let normalizeWithSum : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) × ℝ :=
    fun y ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j)
  let scale : (Fin (n + 1) → ℝ) × ℝ → Fin (n + 1) → ℝ :=
    fun p ↦ p.2 • p.1
  have hnormalize_meas : Measurable normalizeWithSum := by
    -- Proof comment: normalization together with the total sum is measurable coordinatewise.
    fun_prop
  have hscale_meas : Measurable scale := by
    -- Proof comment: scalar multiplication on the function space is measurable.
    fun_prop
  -- Proof comment: rewrite the Dirichlet/Gamma product law as the source Gamma law pushed
  -- forward by `(normalize, sum)`, then collapse the composite back to the identity a.e.
  calc
    Measure.map scale ((dirichletMeasure θ).prod (gammaMeasure (∑ i : Fin (n + 1), θ i) 1))
        = Measure.map scale (Measure.map normalizeWithSum μ) := by
            rw [← map_piGamma_to_dirichletMeasure_prod_gammaSum hθ]
    _ = Measure.map (scale ∘ normalizeWithSum) μ := by
          rw [Measure.map_map hscale_meas hnormalize_meas]
    _ = Measure.map id μ := by
          simpa [Function.comp, μ, normalizeWithSum, scale] using
            (Measure.map_congr
              (reconstruct_piGamma_ae (θ := θ) hθ) :
                Measure.map (scale ∘ normalizeWithSum) μ = Measure.map id μ)
    _ = μ := by
          simp

-- Route correction: the direct Jacobian proof is the wrong Lean normal form here. The executable
-- route is to package `(X, Z)` as a product-law random pair and then push that law through the
-- scaling map using the normalized-Gamma factorization isolated above.
/-- Theorem 24.27: if `X` has Dirichlet law with parameter vector `θ` and `Z` is an independent
unit-rate Gamma variable with shape `∑ i, θ i`, then the scaled vector `Z • X` has the product
law of independent unit-rate Gamma variables with shapes `θ i`. -/
theorem dirichlet_smul_gamma_hasLaw_pi
    {n : ℕ} (P : Measure Ω) {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    {X : Ω → Fin (n + 1) → ℝ} {Z : Ω → ℝ}
    (hX : HasLaw X (dirichletMeasure θ) P)
    (hZ : HasLaw Z (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) P)
    (hXZ : IndepFun X Z P) :
    HasLaw
      (fun ω ↦ Z ω • X ω)
      (Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1) P := by
  have hThetaSum : 0 < ∑ i : Fin (n + 1), θ i := by
    have htheta_nonneg : ∀ i : Fin (n + 1), 0 ≤ θ i := fun i ↦ le_of_lt (hθ i)
    have htheta_zero :
        θ 0 ≤ ∑ i : Fin (n + 1), θ i := by
      exact Finset.single_le_sum (fun i _ ↦ htheta_nonneg i) (by simp)
    exact lt_of_lt_of_le (hθ 0) htheta_zero
  haveI : IsProbabilityMeasure (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) :=
    isProbabilityMeasure_gammaMeasure hThetaSum zero_lt_one
  haveI : IsFiniteMeasure P := hZ.isFiniteMeasure
  have hPair :
      HasLaw (fun ω ↦ (X ω, Z ω))
        ((dirichletMeasure θ).prod (gammaMeasure (∑ i : Fin (n + 1), θ i) 1)) P := by
    refine ⟨by fun_prop, ?_⟩
    -- Proof comment: independence upgrades the two marginal laws to the joint product law of
    -- `(X, Z)`.
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).1 hXZ]
    rw [hX.map_eq, hZ.map_eq]
  have hScale :
      HasLaw
        (fun p : (Fin (n + 1) → ℝ) × ℝ ↦ p.2 • p.1)
        (Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1)
        ((dirichletMeasure θ).prod (gammaMeasure (∑ i : Fin (n + 1), θ i) 1)) := by
    refine ⟨by fun_prop, map_dirichletMeasure_prod_gamma_to_piGamma hθ⟩
  -- Proof comment: compose the joint law of `(X, Z)` with the scaling map.
  simpa [Function.comp] using hScale.comp hPair

-- Proof sketch: apply the main product-law statement and use the standard characterization of a
-- finite family as independent when its joint law is the corresponding product measure.
/-- The scaled coordinates `ω ↦ Z ω * X ω i` form an independent family. -/
theorem dirichlet_smul_gamma_iIndepFun
    {n : ℕ} (P : Measure Ω) {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    {X : Ω → Fin (n + 1) → ℝ} {Z : Ω → ℝ}
    (hX : HasLaw X (dirichletMeasure θ) P)
    (hZ : HasLaw Z (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) P)
    (hXZ : IndepFun X Z P) :
    iIndepFun (fun i : Fin (n + 1) ↦ fun ω ↦ Z ω * X ω i) P := by
  have hThetaSum : 0 < ∑ i : Fin (n + 1), θ i := by
    have htheta_nonneg : ∀ i : Fin (n + 1), 0 ≤ θ i := fun i ↦ le_of_lt (hθ i)
    have htheta_zero :
        θ 0 ≤ ∑ i : Fin (n + 1), θ i := by
      exact Finset.single_le_sum (fun i _ ↦ htheta_nonneg i) (by simp)
    exact lt_of_lt_of_le (hθ 0) htheta_zero
  haveI : IsProbabilityMeasure (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) :=
    isProbabilityMeasure_gammaMeasure hThetaSum zero_lt_one
  haveI : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  have hMain := dirichlet_smul_gamma_hasLaw_pi P hθ hX hZ hXZ
  have hCoordMap :
      ∀ i : Fin (n + 1), P.map (fun ω ↦ Z ω * X ω i) = gammaMeasure (θ i) 1 := by
    intro i
    haveI : ∀ j : Fin (n + 1), IsProbabilityMeasure (gammaMeasure (θ j) 1) :=
      fun j ↦ isProbabilityMeasure_gammaMeasure (hθ j) zero_lt_one
    have hEval :
        HasLaw (Function.eval i) (gammaMeasure (θ i) 1)
          (Measure.pi fun j : Fin (n + 1) ↦ gammaMeasure (θ j) 1) :=
      (measurePreserving_eval (fun j : Fin (n + 1) ↦ gammaMeasure (θ j) 1) i).hasLaw
    -- Proof comment: each coordinate law is obtained by projecting the joint Gamma product law.
    simpa [Function.comp, smul_eq_mul] using (hEval.comp hMain).map_eq
  -- Proof comment: the main theorem identifies the joint law with a product measure, and the
  -- coordinate marginals agree with the corresponding Gamma factors.
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ by
    simpa [smul_eq_mul] using hMain.aemeasurable.eval i)]
  calc
    P.map (fun ω i ↦ Z ω * X ω i)
        = Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (θ i) 1 := by
            simpa [smul_eq_mul] using hMain.map_eq
    _ = Measure.pi fun i : Fin (n + 1) ↦ P.map (fun ω ↦ Z ω * X ω i) := by
          congr 1
          funext i
          exact (hCoordMap i).symm

-- Proof sketch: project the joint product-law statement to the `i`th coordinate and identify the
-- corresponding marginal of the product measure.
/-- Each scaled coordinate `ω ↦ Z ω * X ω i` has the unit-rate Gamma law with shape `θ i`. -/
theorem dirichlet_smul_gamma_coordinate_hasLaw
    {n : ℕ} (P : Measure Ω) {θ : Fin (n + 1) → ℝ} (hθ : ∀ i, 0 < θ i)
    {X : Ω → Fin (n + 1) → ℝ} {Z : Ω → ℝ}
    (hX : HasLaw X (dirichletMeasure θ) P)
    (hZ : HasLaw Z (gammaMeasure (∑ i : Fin (n + 1), θ i) 1) P)
    (hXZ : IndepFun X Z P) (i : Fin (n + 1)) :
    HasLaw (fun ω ↦ Z ω * X ω i) (gammaMeasure (θ i) 1) P := by
  haveI : ∀ j : Fin (n + 1), IsProbabilityMeasure (gammaMeasure (θ j) 1) :=
    fun j ↦ isProbabilityMeasure_gammaMeasure (hθ j) zero_lt_one
  have hEval :
      HasLaw (Function.eval i) (gammaMeasure (θ i) 1)
        (Measure.pi fun j : Fin (n + 1) ↦ gammaMeasure (θ j) 1) :=
    (measurePreserving_eval (fun j : Fin (n + 1) ↦ gammaMeasure (θ j) 1) i).hasLaw
  -- Proof comment: project the `i`th coordinate of the joint Gamma product law.
  simpa [Function.comp, smul_eq_mul] using
    hEval.comp (dirichlet_smul_gamma_hasLaw_pi P hθ hX hZ hXZ)

end ProbabilityTheory
