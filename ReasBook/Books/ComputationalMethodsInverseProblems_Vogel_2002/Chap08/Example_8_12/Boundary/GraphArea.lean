/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Convex.Measure

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace VariationalRegularization.GraphArea

/-- The horizontal identity in a graph derivative makes it expanding. -/
lemma graph_derivative_expands {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1))
    (hcoord : ∀ v j, A v (i.succAbove j) = v j) (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ≤ ‖A v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succAbove _ i]
  simp only [hcoord]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The Gram determinant of a graph derivative is one plus its squared slope. -/
lemma normDet_sq_of_graph_coordinates {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1))
    (hcoord : ∀ v j, A v (i.succAbove j) = v j) :
    A.normDet ^ 2 = 1 + ∑ j : Fin n, (A (EuclideanSpace.single j 1) i) ^ 2 := by
  classical
  let a : Fin n → ℝ := fun j ↦ A (EuclideanSpace.single j 1) i
  have hgram : Matrix.gram ℝ (fun j ↦ A (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      1 + Matrix.replicateCol Unit a * Matrix.replicateRow Unit a := by
    ext j k
    simp only [Matrix.gram_apply, EuclideanSpace.basisFun_apply]
    change (∑ l : Fin (n + 1), A (EuclideanSpace.single k 1) l *
      A (EuclideanSpace.single j 1) l) = _
    rw [Fin.sum_univ_succAbove _ i]
    simp only [hcoord, PiLp.single_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    by_cases hjk : j = k
    · subst k
      simp [a, mul_comm, add_comm]
    · simp [hjk, Ne.symm hjk, a, mul_comm]
  have hsq : A.normDet ^ 2 =
      (Matrix.gram ℝ (fun j ↦ A (EuclideanSpace.basisFun (Fin n) ℝ j))).det := by
    simpa using A.toLinearMap.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
  rw [hsq, hgram, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [a, dotProduct, pow_two]

/-- Express the graph Jacobian using a nonzero normal coordinate. -/
lemma normDet_eq_normal_ratio {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) (N : EuclideanSpace ℝ (Fin (n + 1))) (σ : ℝ)
    (hcoord : ∀ v j, A v (i.succAbove j) = v j)
    (htangent : ∀ j, N (i.succAbove j) + N i * A (EuclideanSpace.single j 1) i = 0)
    (hσ : σ ^ 2 = 1) (hpos : 0 < σ * N i) :
    A.normDet = ‖N‖ / (σ * N i) := by
  have hNsq : ‖N‖ ^ 2 = N i ^ 2 +
      ∑ j : Fin n, N i ^ 2 * (A (EuclideanSpace.single j 1) i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succAbove _ i]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj : N (i.succAbove j) = -(N i * A (EuclideanSpace.single j 1) i) := by
      linarith [htangent j]
    rw [hj]
    ring
  rw [← Finset.mul_sum] at hNsq
  have hs : (A.normDet * (σ * N i)) ^ 2 = ‖N‖ ^ 2 := by
    rw [mul_pow, mul_pow, hσ, one_mul, normDet_sq_of_graph_coordinates A i hcoord, hNsq]
    ring
  apply (eq_div_iff hpos.ne').mpr
  exact (sq_eq_sq₀ (mul_nonneg A.toLinearMap.normDet_nonneg hpos.le) (norm_nonneg N)).mp hs

/-- Local domination of Borel measures glues over a second-countable space. -/
lemma measure_le_of_locally_le {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X)
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ t, MeasurableSet t → t ⊆ U → μ t ≤ ν t) : μ ≤ ν := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hi =>
    haveI := hi
    simp only [Subsingleton.elim μ ν, le_refl]
  | inr hi =>
    haveI := hi
    choose U hU hxU hle using h
    obtain ⟨c, hc⟩ := isLindelof_univ.indexed_countable_subcover U hU
      (show (univ : Set X) ⊆ ⋃ x, U x from fun x _ ↦ mem_iUnion.mpr ⟨x, hxU x⟩)
    let V : ℕ → Set X := disjointed (fun n ↦ U (c n))
    have hV : ∀ n, MeasurableSet (V n) :=
      MeasurableSet.disjointed (fun n ↦ (hU (c n)).measurableSet)
    have hcover : ⋃ n, V n = univ := by
      rw [iUnion_disjointed]
      exact eq_univ_of_univ_subset hc
    apply Measure.le_iff.mpr
    intro t ht
    have htcover : t = ⋃ n, t ∩ V n := by rw [← inter_iUnion, hcover, inter_univ]
    calc
      μ t = ∑' n, μ (t ∩ V n) := by
        calc
          μ t = μ (⋃ n, t ∩ V n) := congrArg μ htcover
          _ = _ := measure_iUnion
            (pairwise_disjoint_mono (disjoint_disjointed _) (fun _ ↦ inter_subset_right))
            (fun n ↦ ht.inter (hV n))
      _ ≤ ∑' n, ν (t ∩ V n) := ENNReal.tsum_le_tsum (fun n ↦
        hle (c n) _ (ht.inter (hV n))
          (inter_subset_right.trans (disjointed_subset _ n)))
      _ = ν t := by
        calc
          _ = ν (⋃ n, t ∩ V n) := (measure_iUnion
            (pairwise_disjoint_mono (disjoint_disjointed _) (fun _ ↦ inter_subset_right))
            (fun n ↦ ht.inter (hV n))).symm
          _ = ν t := congrArg ν htcover.symm

/-- Hausdorff measure comparison through two injective parameterizations. -/
lemma image_measure_le_of_dist_le {n m : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {K : ℝ≥0}
    (hg : InjOn g s)
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ K * ‖g x - g y‖) :
    Measure.euclideanHausdorffMeasure n (f '' s) ≤
      (K : ℝ≥0∞) ^ n * Measure.euclideanHausdorffMeasure n (g '' s) := by
  classical
  let k := f ∘ Function.invFunOn g s
  have hk : LipschitzOnWith K k (g '' s) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa [k, hg.leftInvOn_invFunOn hx, hg.leftInvOn_invFunOn hy] using h x hx y hy
  have himage : k '' (g '' s) = f '' s := by
    rw [image_comp, hg.invFunOn_image (Subset.refl s)]
  have hh := hk.hausdorffMeasure_image_le (d := (n : ℝ)) (by positivity)
  rw [himage] at hh
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  simpa only [ENNReal.rpow_natCast, ENNReal.smul_def, smul_eq_mul, mul_assoc,
    mul_left_comm] using
    mul_le_mul_right hh
      (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (Measure.hausdorffMeasure (n : ℝ)))

/-- A map close to an expanding linear map has the same local area factor,
up to the usual Lipschitz distortion. -/
lemma approximatesLinearOn_image_bounds {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ≥0}
    (hδ : (δ : ℝ) < 1) (hf : InjOn f s)
    (hA : ∀ v, ‖v‖ ≤ ‖A v‖) (h : ApproximatesLinearOn f A s δ) :
    Measure.euclideanHausdorffMeasure n (f '' s) ≤
        ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n * ENNReal.ofReal A.normDet * volume s ∧
      ENNReal.ofReal A.normDet * volume s ≤
        (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n *
          Measure.euclideanHausdorffMeasure n (f '' s) := by
  have hAi : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change A v = 0 at hv
    have hv0 := hA v
    rw [hv, norm_zero] at hv0
    exact norm_eq_zero.mp (le_antisymm hv0 (norm_nonneg _))
  have hlinear : Measure.euclideanHausdorffMeasure n (A '' s) =
      ENNReal.ofReal A.normDet * volume s := by
    simpa only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] using
      A.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s
  constructor
  · have hupper : ∀ x ∈ s, ∀ y ∈ s,
        ‖f x - f y‖ ≤ (1 + δ : ℝ≥0) * ‖A x - A y‖ := by
      intro x hx y hy
      have he := h x hx y hy
      have ha := hA (x - y)
      rw [map_sub] at he ha
      have hn := norm_add_le (f x - f y - A (x - y)) (A (x - y))
      rw [sub_add_cancel, map_sub] at hn
      simp only [NNReal.coe_add, NNReal.coe_one]
      calc
        _ ≤ ‖f x - f y - (A x - A y)‖ + ‖A x - A y‖ := hn
        _ ≤ (δ : ℝ) * ‖x - y‖ + ‖A x - A y‖ := add_le_add he le_rfl
        _ ≤ (δ : ℝ) * ‖A x - A y‖ + ‖A x - A y‖ :=
          add_le_add (mul_le_mul_of_nonneg_left ha δ.2) le_rfl
        _ = _ := by ring
    simpa only [hlinear, mul_assoc] using image_measure_le_of_dist_le hAi.injOn hupper
  · have hlower : ∀ x ∈ s, ∀ y ∈ s,
        ‖A x - A y‖ ≤ ((1 - δ)⁻¹ : ℝ≥0) * ‖f x - f y‖ := by
      intro x hx y hy
      have he := h x hx y hy
      have ha := hA (x - y)
      rw [map_sub] at he ha
      have hn := norm_sub_le (f x - f y) (f x - f y - A (x - y))
      rw [sub_sub_cancel, map_sub] at hn
      rw [NNReal.coe_inv, NNReal.coe_sub (by exact_mod_cast hδ.le), NNReal.coe_one]
      apply (le_inv_mul_iff₀ (by linarith : 0 < 1 - (δ : ℝ))).mpr
      have hh : ‖A x - A y‖ ≤ ‖f x - f y‖ + (δ : ℝ) * ‖A x - A y‖ :=
        hn.trans (add_le_add le_rfl (he.trans (mul_le_mul_of_nonneg_left ha δ.2)))
      nlinarith only [hh]
    simpa only [hlinear] using image_measure_le_of_dist_le hf hlower

/-- The area measure pulled back by an injective immersion. The lower bound
on its derivative is convenient for graph maps, whose horizontal part is the
identity. The density is specified independently, allowing a geometric formula
for it to be substituted later. -/
theorem comap_area_eq_withDensity {n m : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsOpen S)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : InjOn f S) (hfc : ContinuousOn f S) (hw : ContinuousOn w S)
    (hwpos : ∀ x ∈ S, 0 < w x)
    (hderiv : ∀ x ∈ S, HasStrictFDerivAt f (fderiv ℝ f x) x)
    (hexpand : ∀ x ∈ S, ∀ v, ‖v‖ ≤ ‖fderiv ℝ f x v‖)
    (hnorm : ∀ x ∈ S, (fderiv ℝ f x).normDet = w x) :
    Measure.comap (fun x : S ↦ f x) (Measure.euclideanHausdorffMeasure n) =
      (Measure.comap ((↑) : S → EuclideanSpace ℝ (Fin n)) volume).withDensity
        (fun x : S ↦ ENNReal.ofReal (w x)) := by
  classical
  let μ : Measure S := Measure.comap (fun x : S ↦ f x) (Measure.euclideanHausdorffMeasure n)
  let β : Measure S := Measure.comap ((↑) : S → EuclideanSpace ℝ (Fin n)) volume
  let ν : Measure S := β.withDensity (fun x : S ↦ ENNReal.ofReal (w x))
  have hfS : MeasurableEmbedding (fun x : S ↦ f x) :=
    hfc.measurableEmbedding hS.measurableSet hf
  have hcoe : MeasurableEmbedding ((↑) : S → EuclideanSpace ℝ (Fin n)) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hb : ∀ (δ : ℝ≥0), 0 < δ → (δ : ℝ) < 1 →
      μ ≤ (((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (n + 1)) • ν ∧
      ν ≤ (((1 + δ : ℝ≥0) : ℝ≥0∞) * (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n) • μ := by
    intro δ hδpos hδ
    have hlocal : ∀ x : S, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
        ∀ t, MeasurableSet t → t ⊆ U →
          μ t ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (n + 1) * ν t ∧
          ν t ≤ (((1 + δ : ℝ≥0) : ℝ≥0∞) *
            (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n) * μ t := by
      intro x
      let A := fderiv ℝ f x
      have herror := (hderiv x x.2).sub A.hasStrictFDerivAt
      rw [sub_self] at herror
      obtain ⟨V, hV, hVl⟩ := herror.exists_lipschitzOnWith_of_nnnorm_lt δ
        (by simpa using hδpos)
      have happ : ApproximatesLinearOn f A V δ := hVl.approximatesLinearOn
      have hmult : w x < (1 + (δ : ℝ)) * w x := by
        nlinarith [hwpos x x.2, (show 0 < (δ : ℝ) from hδpos)]
      have hwc : ContinuousAt w (x : EuclideanSpace ℝ (Fin n)) :=
        (hw x x.2).continuousAt (hS.mem_nhds x.2)
      have hlo := continuousAt_const.eventually_lt (hwc.const_mul (1 + (δ : ℝ))) hmult
      have hup := hwc.eventually_lt continuousAt_const hmult
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hlo.and hup))
      let U : Set S := ((↑) : S → EuclideanSpace ℝ (Fin n)) ⁻¹' Metric.ball x r
      refine ⟨U, Metric.isOpen_ball.preimage continuous_subtype_val, Metric.mem_ball_self hr, ?_⟩
      intro t ht htU
      let b : Set (EuclideanSpace ℝ (Fin n)) := ((↑) : S → EuclideanSpace ℝ (Fin n)) '' t
      have hbV : b ⊆ V := by
        rintro y ⟨z, hz, rfl⟩
        exact (hball (htU hz)).1
      have hbS : b ⊆ S := by rintro y ⟨z, _, rfl⟩; exact z.2
      have hβt : β t = volume b :=
        Measure.comap_apply _ hcoe.injective (fun _ hs ↦ hcoe.measurableSet_image.mpr hs) _ ht
      have hμt : μ t = Measure.euclideanHausdorffMeasure n (f '' b) := by
        rw [Measure.comap_apply _ hfS.injective (fun _ hs ↦ hfS.measurableSet_image.mpr hs) _ ht]
        congr 1
        exact (image_image f ((↑) : S → EuclideanSpace ℝ (Fin n)) t).symm
      have hlower : ENNReal.ofReal (w x) * β t ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) * ν t := by
        calc
          _ = ∫⁻ _ in t, ENNReal.ofReal (w x) ∂β := by simp
          _ ≤ ∫⁻ z in t, ((1 + δ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (w z) ∂β := by
            apply setLIntegral_mono' ht
            intro z hz
            have hz' := (hball (htU hz)).2.1.le
            have he := ENNReal.ofReal_le_ofReal hz'
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + (δ : ℝ))] at he
            have ha : ENNReal.ofReal (1 + (δ : ℝ)) = ((1 + δ : ℝ≥0) : ℝ≥0∞) := by
              change ENNReal.ofReal (((1 + δ : ℝ≥0) : ℝ)) = _
              exact ENNReal.ofReal_coe_nnreal
            rwa [ha] at he
          _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
            ← withDensity_apply _ ht]
      have hupper : ν t ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) * (ENNReal.ofReal (w x) * β t) := by
        calc
          _ = ∫⁻ z in t, ENNReal.ofReal (w z) ∂β := withDensity_apply _ ht
          _ ≤ ∫⁻ _ in t, ENNReal.ofReal ((1 + (δ : ℝ)) * w x) ∂β := by
            apply setLIntegral_mono' ht
            intro z hz
            exact ENNReal.ofReal_le_ofReal (hball (htU hz)).2.2.le
          _ = _ := by
            rw [setLIntegral_const, ENNReal.ofReal_mul (by positivity)]
            simp only [show 1 + (δ : ℝ) = ((1 + δ : ℝ≥0) : ℝ) by simp,
              ENNReal.ofReal_coe_nnreal, mul_assoc]
      obtain ⟨hu, hl⟩ := approximatesLinearOn_image_bounds hδ (hf.mono hbS)
        (hexpand x x.2) (happ.mono_set hbV)
      rw [hnorm x x.2, ← hβt, ← hμt] at hu hl
      constructor
      · calc
          μ t ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n * (ENNReal.ofReal (w x) * β t) :=
            by simpa only [mul_assoc] using hu
          _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n * (((1 + δ : ℝ≥0) : ℝ≥0∞) * ν t) :=
            mul_le_mul_right hlower _
          _ = _ := by rw [pow_succ]; ac_rfl
      · exact hupper.trans (by
          simpa only [mul_assoc] using mul_le_mul_right hl ((1 + δ : ℝ≥0) : ℝ≥0∞))
    constructor
    · apply measure_le_of_locally_le
      intro x
      obtain ⟨U, hU, hxU, h⟩ := hlocal x
      exact ⟨U, hU, hxU, fun t ht htU ↦ by simpa only [Measure.smul_apply,
        smul_eq_mul] using (h t ht htU).1⟩
    · apply measure_le_of_locally_le
      intro x
      obtain ⟨U, hU, hxU, h⟩ := hlocal x
      exact ⟨U, hU, hxU, fun t ht htU ↦ by simpa only [Measure.smul_apply,
        smul_eq_mul] using (h t ht htU).2⟩
  have hlim₁ : Tendsto (fun δ : ℝ≥0 ↦ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (n + 1))
      (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun δ : ℝ≥0 ↦ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (n + 1)) 0 := by
      fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hlim₂ : Tendsto (fun δ : ℝ≥0 ↦ ((1 + δ : ℝ≥0) : ℝ≥0∞) *
      (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n) (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun δ : ℝ≥0 ↦ (1 + δ) * ((1 - δ)⁻¹) ^ n) 0 := by
      fun_prop (disch := norm_num)
    have hc : Tendsto (fun δ : ℝ≥0 ↦ ((1 + δ : ℝ≥0) : ℝ≥0∞) *
        (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n) (𝓝 0) (𝓝 1) := by
      convert ENNReal.tendsto_coe.2 h.tendsto using 1
      · ext δ
        rw [ENNReal.coe_mul, ENNReal.coe_pow]
      · norm_num
    exact hc.mono_left nhdsWithin_le_nhds
  apply le_antisymm
  · apply Measure.le_iff.mpr
    intro t ht
    have hlim := ENNReal.Tendsto.mul_const (b := ν t) hlim₁ (Or.inl (by simp))
    simp only [one_mul] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ≥0) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with δ hδpos hδ
    simpa only [Measure.smul_apply, smul_eq_mul] using (hb δ hδpos (by exact_mod_cast hδ)).1 t
  · apply Measure.le_iff.mpr
    intro t ht
    have hlim := ENNReal.Tendsto.mul_const (b := μ t) hlim₂ (Or.inl (by simp))
    simp only [one_mul] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ≥0) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with δ hδpos hδ
    simpa only [Measure.smul_apply, smul_eq_mul] using (hb δ hδpos (by exact_mod_cast hδ)).2 t

/-- The image form of the local immersion area formula. -/
theorem image_area_eq_lintegral {n m : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsOpen S)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : InjOn f S) (hfc : ContinuousOn f S) (hw : ContinuousOn w S)
    (hwpos : ∀ x ∈ S, 0 < w x)
    (hderiv : ∀ x ∈ S, HasStrictFDerivAt f (fderiv ℝ f x) x)
    (hexpand : ∀ x ∈ S, ∀ v, ‖v‖ ≤ ‖fderiv ℝ f x v‖)
    (hnorm : ∀ x ∈ S, (fderiv ℝ f x).normDet = w x)
    {t : Set (EuclideanSpace ℝ (Fin n))} (ht : MeasurableSet t) (htS : t ⊆ S) :
    Measure.euclideanHausdorffMeasure n (f '' t) =
      ∫⁻ x in t, ENNReal.ofReal (w x) ∂volume := by
  let T : Set S := ((↑) : S → EuclideanSpace ℝ (Fin n)) ⁻¹' t
  have hT : MeasurableSet T := measurable_subtype_coe ht
  have hi : ((↑) : S → EuclideanSpace ℝ (Fin n)) '' T = t := by
    ext x
    simp only [mem_image, mem_preimage, T, Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨_, hx⟩; exact hx
    · intro hx; exact ⟨htS hx, hx⟩
  have hfS : MeasurableEmbedding (fun x : S ↦ f x) :=
    hfc.measurableEmbedding hS.measurableSet hf
  have heq := congrArg (fun μ : Measure S ↦ μ T)
    (comap_area_eq_withDensity hS hf hfc hw hwpos hderiv hexpand hnorm)
  rw [hfS.comap_apply, withDensity_apply _ hT,
    setLIntegral_subtype hS.measurableSet T (fun x ↦ ENNReal.ofReal (w x)), hi] at heq
  have hmap : (fun x : S ↦ f x) '' T = f '' t := by
    rw [← hi, image_image]
  rwa [hmap] at heq

/-- Lipschitz images of Lebesgue null sets have zero area in the source dimension. -/
lemma area_image_eq_zero_of_lipschitzOnWith {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : volume s = 0) :
    Measure.euclideanHausdorffMeasure n (f '' s) = 0 := by
  have hh := hf.hausdorffMeasure_image_le (d := (n : ℝ)) (by positivity)
  have hscale := mul_le_mul_right hh
    (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (Measure.hausdorffMeasure (n : ℝ)))
  have hzero : Measure.euclideanHausdorffMeasure n s = 0 := by
    rwa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at hzero ⊢
  apply le_antisymm _ (by positivity)
  calc
    _ ≤ (K : ℝ≥0∞) ^ n *
        ((Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (Measure.hausdorffMeasure (n : ℝ)) : ℝ≥0∞) *
            Measure.hausdorffMeasure (n : ℝ) s) := by
      simpa only [ENNReal.rpow_natCast, mul_assoc, mul_left_comm] using hscale
    _ = 0 := by rw [hzero, mul_zero]

/-- Area formula on a compact convex graph patch. Its frontier is Lebesgue
null and has null image, so differentiability is only needed on the interior. -/
theorem map_withDensity_area_of_compact_convex {n m : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsCompact C) (hconv : Convex ℝ C)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hf : InjOn f C) (hfc : ContinuousOn f C) (hlip : LipschitzOnWith K f C)
    (hw : ContinuousOn w (interior C)) (hwpos : ∀ x ∈ interior C, 0 < w x)
    (hderiv : ∀ x ∈ interior C, HasStrictFDerivAt f (fderiv ℝ f x) x)
    (hexpand : ∀ x ∈ interior C, ∀ v, ‖v‖ ≤ ‖fderiv ℝ f x v‖)
    (hnorm : ∀ x ∈ interior C, (fderiv ℝ f x).normDet = w x) :
    Measure.map f ((volume.restrict C).withDensity (fun x ↦ ENNReal.ofReal (w x))) =
      (Measure.euclideanHausdorffMeasure n).restrict (f '' C) := by
  have hfront : volume (frontier C) = 0 := Convex.addHaar_frontier volume hconv
  have himage : ∀ t, MeasurableSet t → t ⊆ C →
      Measure.euclideanHausdorffMeasure n (f '' t) =
        ∫⁻ x in t, ENNReal.ofReal (w x) ∂volume := by
    intro t ht htC
    have hdiff : volume (t \ interior C) = 0 := by
      have hs : t \ interior C ⊆ frontier C := by
        intro x hx
        exact ⟨subset_closure (htC hx.1), hx.2⟩
      exact measure_mono_null hs hfront
    have hdiff_image : Measure.euclideanHausdorffMeasure n (f '' (t \ interior C)) = 0 :=
      area_image_eq_zero_of_lipschitzOnWith (hlip.mono (sdiff_subset.trans htC)) hdiff
    have hae : (fun x ↦ x ∈ t) =ᵐ[volume] (fun x ↦ x ∈ t ∩ interior C) := by
      have hnot : ∀ᵐ x ∂volume, x ∉ frontier C := by
        rw [ae_iff]
        simpa using hfront
      filter_upwards [hnot] with x hx
      apply propext
      constructor
      · intro hxt
        exact ⟨hxt, by by_contra hxi; exact hx ⟨subset_closure (htC hxt), hxi⟩⟩
      · exact fun hx ↦ hx.1
    calc
      _ = Measure.euclideanHausdorffMeasure n (f '' (t ∩ interior C)) := by
        calc
          _ = Measure.euclideanHausdorffMeasure n
              (f '' (t ∩ interior C) ∪ f '' (t \ interior C)) := by
            rw [← image_union, inter_union_sdiff]
          _ = _ := le_antisymm
            ((measure_union_le _ _).trans (by rw [hdiff_image, add_zero]))
            (measure_mono subset_union_left)
      _ = ∫⁻ x in t ∩ interior C, ENNReal.ofReal (w x) ∂volume :=
        image_area_eq_lintegral isOpen_interior (hf.mono interior_subset)
          (hfc.mono interior_subset) hw hwpos hderiv hexpand hnorm
          (ht.inter isOpen_interior.measurableSet) inter_subset_right
      _ = _ := by
        have hrestr : volume.restrict t = volume.restrict (t ∩ interior C) :=
          Measure.restrict_congr_set (s := t) (t := t ∩ interior C) (by
            filter_upwards [hae] with x hx
            exact hx)
        rw [hrestr]
  have hfa : AEMeasurable f (volume.restrict C) := hfc.aemeasurable hC.measurableSet
  have hfw : AEMeasurable f
      ((volume.restrict C).withDensity (fun x ↦ ENNReal.ofReal (w x))) :=
    hfa.mono' (withDensity_absolutelyContinuous _ _)
  have hfC := hfc.measurableEmbedding hC.measurableSet hf
  have hcoe := MeasurableEmbedding.subtype_coe hC.measurableSet
  ext t ht
  have hpre : MeasurableSet (f ⁻¹' t ∩ C) := by
    have he : f ⁻¹' t ∩ C = ((↑) : C → EuclideanSpace ℝ (Fin n)) ''
        ((fun x : C ↦ f x) ⁻¹' t) := by ext x; simp
    rw [he]
    exact hcoe.measurableSet_image.mpr (hfC.measurable ht)
  have hpi : f '' (f ⁻¹' t ∩ C) = t ∩ f '' C := by
    ext x
    simp only [mem_image, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨y, ⟨hy, hyC⟩, rfl⟩; exact ⟨hy, y, hyC, rfl⟩
    · rintro ⟨hx, y, hyC, rfl⟩; exact ⟨y, ⟨hx, hyC⟩, rfl⟩
  rw [Measure.map_apply_of_aemeasurable hfw ht,
    withDensity_apply₀ _ (hfa.nullMeasurableSet_preimage ht),
    Measure.restrict_restrict₀ (hfa.nullMeasurableSet_preimage ht), Measure.restrict_apply ht,
    ← hpi, himage _ hpre inter_subset_right]

end VariationalRegularization.GraphArea
