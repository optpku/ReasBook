/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
attribute [local instance] Classical.propDecidable

/-- Definition 21.52 (1): the first-variation path `t ↦ V_t^1(G)` of a continuous real-valued
path on `[0, ∞)` is the canonical signed-variation path `variationOnFromTo G univ 0`. -/
def variationProcess (G : PathSpace) : NNReal → ℝ :=
  variationOnFromTo G univ 0

/-- Evaluating `variationProcess G` at time `t` gives the total variation of `G` on `[0, t]`. -/
theorem variationProcess_eq_toReal_eVariationOn_Icc (G : PathSpace) (t : NNReal) :
    variationProcess G t = (eVariationOn G (Icc 0 t)).toReal := by
  -- Unfold the definition once and rewrite the owner interval to `[0, t]`.
  rw [variationProcess, variationOnFromTo.eq_of_le G univ (show (0 : NNReal) ≤ t by exact bot_le)]
  simp

/-- Definition 21.52 (2): for paths on `[0, ∞)`, the source condition "locally finite variation"
is exactly the canonical owner property `LocallyBoundedVariationOn G univ`. -/
theorem locallyBoundedVariationOn_univ_iff_forall_boundedVariationOn_Icc_zero (G : PathSpace) :
    LocallyBoundedVariationOn G univ ↔ ∀ t : NNReal, BoundedVariationOn G (Icc 0 t) := by
  constructor
  · intro hG t
    -- Evaluate the owner predicate at the interval endpoints `0` and `t`.
    simpa using hG 0 t (mem_univ _) (mem_univ _)
  · intro hG a b _ _
    -- Any compact interval `[a, b]` sits inside `[0, max a b]` on `NNReal`.
    refine (hG (max a b)).mono ?_
    intro x hx
    exact ⟨by simp, hx.2.2.trans (le_max_right a b)⟩

/-- Helper for Remark 21.54: a locally integrable density has a continuous interval-integral
primitive. -/
theorem continuousPrimitiveOfLocallyIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) :
    Continuous (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, f s) := by
  -- Local integrability gives interval integrability on every compact interval.
  refine intervalIntegral.continuous_primitive ?_ 0
  intro a b
  exact (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

/-- The path obtained by integrating a real function from `0` to `t`. -/
def indefiniteIntegralPath (f : ℝ → ℝ) : PathSpace :=
  if hf : LocallyIntegrable f volume then
    { toFun := fun t ↦ ∫ s in (0 : ℝ)..(t : ℝ), f s
      continuous_toFun := (continuousPrimitiveOfLocallyIntegrable hf).comp continuous_subtype_val }
  else 0

/-- Helper for Remark 21.54: under local integrability, the repaired path agrees with the intended
primitive `t ↦ ∫_0^t f`. -/
theorem indefiniteIntegralPath_apply_of_locallyIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (t : NNReal) :
    indefiniteIntegralPath f t = ∫ s in (0 : ℝ)..(t : ℝ), f s := by
  -- Rewrite through the repaired total definition.
  simp [indefiniteIntegralPath, hf]

/-- The positive Jordan-variation part `G_t^+ = (V_t^1(G) + G_t) / 2`. -/
def positiveVariationPart (G : PathSpace) : NNReal → ℝ :=
  fun t ↦ (variationProcess G t + G t) / 2

/-- The negative Jordan-variation part `G_t^- = (V_t^1(G) - G_t) / 2`. -/
def negativeVariationPart (G : PathSpace) : NNReal → ℝ :=
  fun t ↦ (variationProcess G t - G t) / 2

/-- The signed Lebesgue--Stieltjes integral on `[0,t]`, defined from the Jordan decomposition of a
signed measure. -/
def signedLebesgueStieltjesIntegralUpTo
    (F : ℝ → ℝ) (μ : SignedMeasure ℝ) (t : NNReal) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.posPart -
    ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.negPart

/-- Helper for Remark 21.54: each increment of a locally bounded-variation path is controlled by
the variation increment on the same interval. -/
theorem abs_sub_le_variationOnFromTo_of_locallyBoundedVariation
    {G : PathSpace} (hG : LocallyBoundedVariationOn G univ) {s t : NNReal} (hst : s ≤ t) :
    |G t - G s| ≤ variationOnFromTo G univ s t := by
  -- Rewrite the signed variation on `[s, t]` to total variation and compare endpoint distance.
  rw [variationOnFromTo.eq_of_le G univ hst, Set.univ_inter, ← Real.dist_eq]
  rw [dist_comm, dist_edist]
  have hedist : edist (G s) (G t) ≤ eVariationOn G (univ ∩ Icc s t) := by
    apply eVariationOn.edist_le G
    · exact ⟨mem_univ _, ⟨le_rfl, hst⟩⟩
    · exact ⟨mem_univ _, ⟨hst, le_rfl⟩⟩
  simpa [Set.univ_inter] using ENNReal.toReal_mono (hG s t (mem_univ _) (mem_univ _)) hedist

/-- Helper for Remark 21.54: on `[s, t]`, the variation of `Gplus - Gminus` is bounded by the
sum of the monotone increments of `Gplus` and `Gminus`. -/
theorem eVariationOn_Icc_sub_le_of_monotone
    {G Gplus Gminus : PathSpace} (hG : G = Gplus - Gminus) (hGplus_mono : Monotone Gplus)
    (hGminus_mono : Monotone Gminus) {s t : NNReal} (hst : s ≤ t) :
    eVariationOn G (Icc s t) ≤
      ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s)) := by
  -- Rewrite `G` to `Gplus - Gminus` and reduce the claim to arbitrary partition sums.
  rw [hG]
  have hGplus_nonneg : 0 ≤ Gplus t - Gplus s := sub_nonneg_of_le (hGplus_mono hst)
  have hGminus_nonneg : 0 ≤ Gminus t - Gminus s := sub_nonneg_of_le (hGminus_mono hst)
  have hGplus_var :
      eVariationOn Gplus (Icc s t) ≤ ENNReal.ofReal (Gplus t - Gplus s) := by
    -- Monotonicity turns the total variation of `Gplus` on `[s,t]` into its endpoint increment.
    simpa [Set.univ_inter] using
      (MonotoneOn.eVariationOn_le (f := Gplus) (s := univ) (hGplus_mono.monotoneOn univ)
        (a := s) (b := t) (mem_univ _) (mem_univ _))
  have hGminus_var :
      eVariationOn Gminus (Icc s t) ≤ ENNReal.ofReal (Gminus t - Gminus s) := by
    -- The same endpoint control applies to `Gminus`.
    simpa [Set.univ_inter] using
      (MonotoneOn.eVariationOn_le (f := Gminus) (s := univ) (hGminus_mono.monotoneOn univ)
        (a := s) (b := t) (mem_univ _) (mem_univ _))
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    ∑ i ∈ Finset.range n, edist ((Gplus - Gminus) (u (i + 1))) ((Gplus - Gminus) (u i))
        ≤ ∑ i ∈ Finset.range n,
            (edist (Gplus (u (i + 1))) (Gplus (u i)) +
              edist (Gminus (u (i + 1))) (Gminus (u i))) := by
      -- Each increment of `Gplus - Gminus` is controlled by the triangle inequality in `ℝ`.
      refine Finset.sum_le_sum fun i hi => ?_
      simpa [Pi.sub_apply] using
        (edist_vsub_vsub_le (Gplus (u (i + 1))) (Gminus (u (i + 1))) (Gplus (u i))
          (Gminus (u i)))
    _ = (∑ i ∈ Finset.range n, edist (Gplus (u (i + 1))) (Gplus (u i))) +
          ∑ i ∈ Finset.range n, edist (Gminus (u (i + 1))) (Gminus (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn Gplus (Icc s t) + eVariationOn Gminus (Icc s t) := by
      -- Both partition sums are bounded by the corresponding total variations.
      exact add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)
    _ ≤ ENNReal.ofReal (Gplus t - Gplus s) + ENNReal.ofReal (Gminus t - Gminus s) := by
      exact add_le_add hGplus_var hGminus_var
    _ = ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s)) := by
      rw [ENNReal.ofReal_add hGplus_nonneg hGminus_nonneg]

-- Proof sketch: view `t ↦ ∫_0^t f(s) ds` as an absolutely continuous path on every compact
-- interval `[0, t]`; its variation on that interval is the integral of `|f|`, and therefore the
-- path has locally bounded variation on `[0, ∞)`.
/-- A locally integrable density defines a path of locally bounded variation on `[0, ∞)`. -/
theorem locallyBoundedVariationOn_univ_indefiniteIntegralPath
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyBoundedVariationOn (indefiniteIntegralPath f) univ := by
  -- It suffices to prove finite variation on each initial interval `[0, t]`.
  rw [locallyBoundedVariationOn_univ_iff_forall_boundedVariationOn_Icc_zero]
  intro t
  let F : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..x, f s
  have hft : IntervalIntegrable f volume (0 : ℝ) t := by
    exact (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hF_bv : BoundedVariationOn F (Set.Icc (0 : ℝ) (t : ℝ)) := by
    -- The real primitive is absolutely continuous on `[0, t]`.
    have hF_ac : AbsolutelyContinuousOnInterval F 0 t := by
      simpa [F] using hft.absolutelyContinuousOnInterval_intervalIntegral (by simp)
    simpa [uIcc_of_le t.2] using hF_ac.boundedVariationOn
  have hEq :
      EqOn (indefiniteIntegralPath f) (fun x : NNReal ↦ F x) (Icc 0 t) := by
    -- On nonnegative times the repaired path is the interval-integral primitive.
    intro x hx
    simpa [F] using indefiniteIntegralPath_apply_of_locallyIntegrable hf x
  have hcomp :
      eVariationOn (indefiniteIntegralPath f) (Icc 0 t) ≤
        eVariationOn F (Set.Icc (0 : ℝ) (t : ℝ)) := by
    -- Compare the NNReal-indexed path with the real primitive through the monotone coercion.
    calc
      eVariationOn (indefiniteIntegralPath f) (Icc 0 t) =
          eVariationOn (fun x : NNReal ↦ F x) (Icc 0 t) :=
        eVariationOn.eq_of_eqOn hEq
      _ ≤ eVariationOn F (Set.Icc (0 : ℝ) (t : ℝ)) := by
        apply eVariationOn.comp_le_of_monotoneOn F (fun x : NNReal ↦ (x : ℝ))
        · intro x hx y hy hxy
          exact_mod_cast hxy
        · intro x hx
          simpa using hx
  exact (hcomp.trans_lt (lt_top_iff_ne_top.mpr hF_bv)).ne

/-- Helper for Remark 21.54: the variation of the real primitive on `[x, y]` is bounded by the
`L¹` mass of `f` on that interval. -/
theorem realPrimitive_eVariationOn_Icc_le_intervalIntegral_abs {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    eVariationOn (fun z : ℝ ↦ ∫ s in (0 : ℝ)..z, f s) (Set.Icc x y) ≤
      ENNReal.ofReal (∫ s in x..y, |f s|) := by
  let F : ℝ → ℝ := fun z ↦ ∫ s in (0 : ℝ)..z, f s
  let H : ℝ → ℝ := fun z ↦ ∫ s in (0 : ℝ)..z, |f s|
  -- Rewrite primitive increments on nonnegative intervals as interval integrals.
  have hIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
      F b - F a = ∫ s in a..b, f s := by
    have h0a : IntervalIntegrable f volume (0 : ℝ) a :=
      (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
    have habInt : IntervalIntegrable f volume a b :=
      (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
    have hadd : F a + ∫ s in a..b, f s = F b := by
      simpa [F] using intervalIntegral.integral_add_adjacent_intervals h0a habInt
    linarith
  have hAbsIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
      H b - H a = ∫ s in a..b, |f s| := by
    have h0a : IntervalIntegrable (fun s ↦ |f s|) volume (0 : ℝ) a :=
      ((hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
    have habInt : IntervalIntegrable (fun s ↦ |f s|) volume a b :=
      ((hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
    have hadd : H a + ∫ s in a..b, |f s| = H b := by
      simpa [H] using intervalIntegral.integral_add_adjacent_intervals h0a habInt
    linarith
  -- The primitive of `|f|` is monotone on `[x, y]`.
  have hH_mono : MonotoneOn H (Set.Icc x y) := by
    intro a ha b hb hab
    have ha0 : 0 ≤ a := hx.trans ha.1
    have hnonneg : 0 ≤ ∫ s in a..b, |f s| := by
      exact intervalIntegral.integral_nonneg hab fun _ _ => abs_nonneg _
    have : 0 ≤ H b - H a := by
      rw [hAbsIncrement ha0 hab]
      exact hnonneg
    linarith
  -- Compare every partition increment with the corresponding increment of `H`, then telescope.
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i)) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal |∫ s in u i..u (i + 1), f s| := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have h0ui : 0 ≤ u i := hx.trans (us i).1
      have hui : u i ≤ u (i + 1) := hu (Nat.le_succ _)
      rw [edist_dist, Real.dist_eq]
      congr 1
      rw [hIncrement h0ui hui]
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (H (u (i + 1)) - H (u i)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have h0ui : 0 ≤ u i := hx.trans (us i).1
      have hui : u i ≤ u (i + 1) := hu (Nat.le_succ _)
      refine ENNReal.ofReal_le_ofReal ?_
      calc
        |∫ s in u i..u (i + 1), f s| ≤ ∫ s in u i..u (i + 1), |f s| :=
          intervalIntegral.abs_integral_le_integral_abs hui
        _ = H (u (i + 1)) - H (u i) := by rw [hAbsIncrement h0ui hui]
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (H (u (i + 1)) - H (u i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact sub_nonneg_of_le (hH_mono (us i) (us (i + 1)) (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (H (u n) - H (u 0)) := by
      rw [Finset.sum_range_sub fun i => H (u i)]
    _ ≤ ENNReal.ofReal (H y - H x) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hun : u n ∈ Set.Icc x y := us n
      have hu0 : u 0 ∈ Set.Icc x y := us 0
      exact sub_le_sub
        (hH_mono hun (by simpa using show y ∈ Set.Icc x y by exact ⟨hxy, le_rfl⟩) hun.2)
        (hH_mono (by simpa using show x ∈ Set.Icc x y by exact ⟨le_rfl, hxy⟩) hu0 hu0.1)
    _ = ENNReal.ofReal (∫ s in x..y, |f s|) := by
      rw [hAbsIncrement hx hxy]

/-- Helper for Remark 21.54: the signed variation increment of the real primitive on `[x, y]`
is controlled by `∫ s in x..y, |f s|`. -/
theorem realPrimitive_variationOnFromTo_le_intervalIntegral_abs {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    variationOnFromTo (fun z : ℝ ↦ ∫ s in (0 : ℝ)..z, f s) univ x y ≤
      ∫ s in x..y, |f s| := by
  have hnonneg : 0 ≤ ∫ s in x..y, |f s| := by
    exact intervalIntegral.integral_nonneg hxy fun _ _ => abs_nonneg _
  -- Rewrite the signed variation to total variation and convert the `ENNReal` bound to `ℝ`.
  rw [variationOnFromTo.eq_of_le _ _ hxy, Set.univ_inter]
  calc
    (eVariationOn (fun z : ℝ ↦ ∫ s in (0 : ℝ)..z, f s) (Set.Icc x y)).toReal ≤
        (ENNReal.ofReal (∫ s in x..y, |f s|)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (realPrimitive_eVariationOn_Icc_le_intervalIntegral_abs hf hx hxy)
    _ = ∫ s in x..y, |f s| := by
      simp [hnonneg]

/-- Helper for Remark 21.54: on `[0, t]`, the variation path of the real primitive is absolutely
continuous. -/
theorem realPrimitiveVariation_absolutelyContinuousOnInterval {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) {t : ℝ} (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval
      (variationOnFromTo (fun z : ℝ ↦ ∫ s in (0 : ℝ)..z, f s) univ 0) 0 t := by
  let s : Set ℝ := Set.Icc 0 t
  let F : ℝ → ℝ := fun z ↦ ∫ s in (0 : ℝ)..z, f s
  let V : ℝ → ℝ := variationOnFromTo F univ 0
  let H : ℝ → ℝ := fun z ↦ ∫ s in (0 : ℝ)..z, |f s|
  have hs0 : (0 : ℝ) ∈ s := by simp [s, ht]
  have hIntAbs : IntervalIntegrable (fun z ↦ |f z|) volume (0 : ℝ) t :=
    ((hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
  have hH_ac : AbsolutelyContinuousOnInterval H 0 t := by
    -- The primitive of `|f|` is absolutely continuous on `[0, t]`.
    simpa [H] using hIntAbs.absolutelyContinuousOnInterval_intervalIntegral (by simp [ht])
  have hH_increment {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      H y - H x = ∫ z in x..y, |f z| := by
    have h0x : IntervalIntegrable (fun z ↦ |f z|) volume (0 : ℝ) x :=
      ((hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
    have hxyInt : IntervalIntegrable (fun z ↦ |f z|) volume x y :=
      ((hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
    have hadd : H x + ∫ z in x..y, |f z| = H y := by
      simpa [H] using intervalIntegral.integral_add_adjacent_intervals h0x hxyInt
    linarith
  -- The real primitive has finite variation on every subinterval of `[0, t]`.
  have hF_loc : LocallyBoundedVariationOn F s := by
    intro a b ha hb
    by_cases hab : a ≤ b
    · have hEq : s ∩ Set.Icc a b = Set.Icc a b := by
        ext z
        constructor
        · intro hz
          exact hz.2
        · intro hz
          exact ⟨⟨ha.1.trans hz.1, hz.2.trans hb.2⟩, hz⟩
      have hbound :
          eVariationOn F (s ∩ Set.Icc a b) ≤ ENNReal.ofReal (∫ z in a..b, |f z|) := by
        simpa [F, hEq] using realPrimitive_eVariationOn_Icc_le_intervalIntegral_abs hf ha.1 hab
      exact (hbound.trans_lt ENNReal.ofReal_lt_top).ne
    · have hsub : (s ∩ Set.Icc a b).Subsingleton :=
        (Set.subsingleton_Icc_of_ge (le_of_not_ge hab)).anti Set.inter_subset_right
      simpa [BoundedVariationOn, eVariationOn.subsingleton F hsub]
  have hV_eq {x : ℝ} (hx : x ∈ s) : variationOnFromTo F s 0 x = V x := by
    -- Restricting the variation to `[0, t]` does not change it before time `x`.
    dsimp [V]
    rw [variationOnFromTo.eq_of_le _ _ hx.1, variationOnFromTo.eq_of_le _ _ hx.1, Set.univ_inter]
    have hSet : s ∩ Set.Icc 0 x = Set.Icc 0 x := by
      ext z
      constructor
      · intro hz
        exact hz.2
      · intro hz
        exact ⟨⟨hz.1, hz.2.trans hx.2⟩, hz⟩
    simp [hSet]
  have hV_diff {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
      V y - V x = variationOnFromTo F univ x y := by
    -- The variation increment from `x` to `y` is the difference of the anchored variation path.
    calc
      V y - V x = variationOnFromTo F s 0 y - variationOnFromTo F s 0 x := by
        rw [hV_eq hy, hV_eq hx]
      _ = variationOnFromTo F s x y := by
        have hadd :=
          variationOnFromTo.add hF_loc (a := 0) (b := x) (c := y) hs0 hx hy
        linarith
      _ = variationOnFromTo F univ x y := by
        rw [variationOnFromTo.eq_of_le _ _ hxy, variationOnFromTo.eq_of_le _ _ hxy, Set.univ_inter]
        have hSet : s ∩ Set.Icc x y = Set.Icc x y := by
          ext z
          constructor
          · intro hz
            exact hz.2
          · intro hz
            exact ⟨⟨hx.1.trans hz.1, hz.2.trans hy.2⟩, hz⟩
        simp [hSet]
  have hV_le {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
      V y - V x ≤ H y - H x := by
    rw [hV_diff hx hy hxy, hH_increment hx.1 hxy]
    simpa [F] using realPrimitive_variationOnFromTo_le_intervalIntegral_abs hf hx.1 hxy
  have hH_mono : MonotoneOn H s := by
    intro x hx y hy hxy
    have hnonneg : 0 ≤ ∫ z in x..y, |f z| := by
      exact intervalIntegral.integral_nonneg hxy fun _ _ => abs_nonneg _
    have : 0 ≤ H y - H x := by
      rw [hH_increment hx.1 hxy]
      exact hnonneg
    linarith
  have hM_mono : MonotoneOn (H - V) s := by
    -- The remainder `H - V` is increasing because every variation increment is bounded by `H`.
    intro x hx y hy hxy
    have hle := hV_le hx hy hxy
    change H x - V x ≤ H y - V y
    linarith
  have hM_dist {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
      dist ((H - V) x) ((H - V) y) ≤ dist (H x) (H y) := by
    rcases le_total x y with hxy | hyx
    · have hHxy : H x ≤ H y := hH_mono hx hy hxy
      have hMxy : (H - V) x ≤ (H - V) y := hM_mono hx hy hxy
      have hVnonneg : 0 ≤ V y - V x := by
        rw [hV_diff hx hy hxy]
        exact variationOnFromTo.nonneg_of_le _ _ hxy
      have : ((H - V) y - (H - V) x) ≤ H y - H x := by
        calc
          ((H - V) y - (H - V) x) = (H y - H x) - (V y - V x) := by
            simp [Pi.sub_apply]
            ring
          _ ≤ H y - H x := sub_le_self _ hVnonneg
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hMxy), Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hHxy)]
      simpa [Pi.sub_apply, sub_eq_add_neg, sub_sub_sub_cancel_right] using this
    · have hHxy : H y ≤ H x := hH_mono hy hx hyx
      have hMxy : (H - V) y ≤ (H - V) x := hM_mono hy hx hyx
      have hVnonneg : 0 ≤ V x - V y := by
        rw [hV_diff hy hx hyx]
        exact variationOnFromTo.nonneg_of_le _ _ hyx
      have : ((H - V) x - (H - V) y) ≤ H x - H y := by
        calc
          ((H - V) x - (H - V) y) = (H x - H y) - (V x - V y) := by
            simp [Pi.sub_apply]
            ring
          _ ≤ H x - H y := sub_le_self _ hVnonneg
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hMxy), Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr hHxy)]
      simpa [Pi.sub_apply, sub_eq_add_neg, sub_sub_sub_cancel_right] using this
  have hM_ac : AbsolutelyContinuousOnInterval (H - V) 0 t := by
    -- Transfer the absolute continuity of `H` to `H - V` via the pointwise distance control.
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    rcases (absolutelyContinuousOnInterval_iff H 0 t).mp hH_ac ε hε with ⟨δ, hδ, hδH⟩
    refine ⟨δ, hδ, ?_⟩
    intro E hE hlen
    have hsum :
        ∑ i ∈ Finset.range E.1, dist ((H - V) (E.2 i).1) ((H - V) (E.2 i).2) ≤
          ∑ i ∈ Finset.range E.1, dist (H (E.2 i).1) (H (E.2 i).2) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hleft : (E.2 i).1 ∈ s := by
        simpa [s, uIcc_of_le ht] using (hE.1 i hi).1
      have hright : (E.2 i).2 ∈ s := by
        simpa [s, uIcc_of_le ht] using (hE.1 i hi).2
      exact hM_dist hleft hright
    exact lt_of_le_of_lt hsum (hδH E hE hlen)
  -- Subtract the absolutely continuous remainder from `H` to recover the variation path.
  have hV_ac : AbsolutelyContinuousOnInterval (H - (H - V)) 0 t := hH_ac.sub hM_ac
  convert hV_ac using 1
  ext x
  dsimp [V, H]
  ring

/-- Helper for Remark 21.54: transporting the `NNReal` path `indefiniteIntegralPath f` to the real
primitive preserves the variation on `[0, t]`. -/
theorem eVariationOn_indefiniteIntegralPath_Icc_eq_realPrimitive {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (t : NNReal) :
    eVariationOn (indefiniteIntegralPath f) (Set.Icc 0 t) =
      eVariationOn (fun x : ℝ ↦ ∫ s in (0 : ℝ)..x, f s) (Set.Icc (0 : ℝ) (t : ℝ)) := by
  have hEq :
      EqOn (indefiniteIntegralPath f)
        (fun x : NNReal ↦ ∫ s in (0 : ℝ)..(x : ℝ), f s) (Set.Icc 0 t) := by
    -- On the target interval, the repaired path is exactly the intended primitive.
    intro x hx
    simpa using indefiniteIntegralPath_apply_of_locallyIntegrable hf x
  have hImage :
      (fun x : NNReal ↦ (x : ℝ)) '' Set.Icc 0 t = Set.Icc (0 : ℝ) (t : ℝ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
      simpa using hy.2
  -- Transport variation through the monotone coercion `NNReal → ℝ`.
  calc
    eVariationOn (indefiniteIntegralPath f) (Set.Icc 0 t) =
        eVariationOn (fun x : NNReal ↦ ∫ s in (0 : ℝ)..(x : ℝ), f s) (Set.Icc 0 t) :=
      eVariationOn.eq_of_eqOn hEq
    _ = eVariationOn (fun x : ℝ ↦ ∫ s in (0 : ℝ)..x, f s) ((fun x : NNReal ↦ (x : ℝ)) '' Set.Icc 0 t) := by
      simpa [Function.comp] using
        (eVariationOn.comp_eq_of_monotoneOn (fun x : ℝ ↦ ∫ s in (0 : ℝ)..x, f s)
          (t := Set.Icc 0 t) (fun x : NNReal ↦ (x : ℝ))
          (fun x hx y hy hxy => by exact_mod_cast hxy) : _)
    _ = eVariationOn (fun x : ℝ ↦ ∫ s in (0 : ℝ)..x, f s) (Set.Icc (0 : ℝ) (t : ℝ)) := by
      rw [hImage]

/-- First part of Remark 21.54: if `G_t = ∫_0^t f(s) ds` for a locally integrable density `f`, then the
variation path of `G` is given by the integral of `|f|`. -/
theorem variationProcess_indefiniteIntegralPath_eq_intervalIntegral_abs
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (t : NNReal) :
    variationProcess (indefiniteIntegralPath f) t = ∫ s in (0 : ℝ)..(t : ℝ), |f s| := by
  by_cases ht0 : (t : ℝ) = 0
  · -- At time `0`, both the variation and the integral vanish.
    have htnn : t = 0 := by
      apply Subtype.ext
      simpa using ht0
    subst htnn
    rw [variationProcess_eq_toReal_eVariationOn_Icc]
    simp
  · have ht : (0 : ℝ) ≤ (t : ℝ) := t.2
    have htpos : (0 : ℝ) < (t : ℝ) := by
      have htne : (t : ℝ) ≠ 0 := by simpa using ht0
      exact lt_of_le_of_ne ht htne.symm
    let s : Set ℝ := Set.Icc 0 (t : ℝ)
    let F : ℝ → ℝ := fun z ↦ ∫ u in (0 : ℝ)..z, f u
    let V : ℝ → ℝ := variationOnFromTo F univ 0
    let H : ℝ → ℝ := fun z ↦ ∫ u in (0 : ℝ)..z, |f u|
    have hs0 : (0 : ℝ) ∈ s := by simp [s, ht]
    have hInt : IntervalIntegrable f volume (0 : ℝ) (t : ℝ) :=
      (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
    have hIntAbs : IntervalIntegrable (fun z ↦ |f z|) volume (0 : ℝ) (t : ℝ) := hInt.abs
    have hV_ac : AbsolutelyContinuousOnInterval V 0 (t : ℝ) := by
      -- The variation path is absolutely continuous by comparison with the primitive of `|f|`.
      simpa [F, V] using realPrimitiveVariation_absolutelyContinuousOnInterval hf ht
    have hH_increment {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
        H y - H x = ∫ z in x..y, |f z| := by
      have h0x : IntervalIntegrable (fun z ↦ |f z|) volume (0 : ℝ) x :=
        ((hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
      have hxyInt : IntervalIntegrable (fun z ↦ |f z|) volume x y :=
        ((hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
      have hadd : H x + ∫ z in x..y, |f z| = H y := by
        simpa [H] using intervalIntegral.integral_add_adjacent_intervals h0x hxyInt
      linarith
    have hF_loc : LocallyBoundedVariationOn F s := by
      -- The interval estimate makes the real primitive locally of bounded variation on `[0, t]`.
      intro a b ha hb
      by_cases hab : a ≤ b
      · have hEq : s ∩ Set.Icc a b = Set.Icc a b := by
          ext z
          constructor
          · intro hz
            exact hz.2
          · intro hz
            exact ⟨⟨ha.1.trans hz.1, hz.2.trans hb.2⟩, hz⟩
        have hbound :
            eVariationOn F (s ∩ Set.Icc a b) ≤ ENNReal.ofReal (∫ z in a..b, |f z|) := by
          simpa [F, hEq] using realPrimitive_eVariationOn_Icc_le_intervalIntegral_abs hf ha.1 hab
        exact (hbound.trans_lt ENNReal.ofReal_lt_top).ne
      · have hsub : (s ∩ Set.Icc a b).Subsingleton :=
          (Set.subsingleton_Icc_of_ge (le_of_not_ge hab)).anti Set.inter_subset_right
        simpa [BoundedVariationOn, eVariationOn.subsingleton F hsub]
    have hV_eq {x : ℝ} (hx : x ∈ s) : variationOnFromTo F s 0 x = V x := by
      -- Restricting to `[0, t]` does not change the anchored variation before time `x`.
      dsimp [V]
      rw [variationOnFromTo.eq_of_le _ _ hx.1, variationOnFromTo.eq_of_le _ _ hx.1, Set.univ_inter]
      have hSet : s ∩ Set.Icc 0 x = Set.Icc 0 x := by
        ext z
        constructor
        · intro hz
          exact hz.2
        · intro hz
          exact ⟨⟨hz.1, hz.2.trans hx.2⟩, hz⟩
      simp [hSet]
    have hV_diff {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
        V y - V x = variationOnFromTo F univ x y := by
      -- The increment of the variation path is the variation on the subinterval `[x, y]`.
      calc
        V y - V x = variationOnFromTo F s 0 y - variationOnFromTo F s 0 x := by
          rw [hV_eq hy, hV_eq hx]
        _ = variationOnFromTo F s x y := by
          have hadd :=
            variationOnFromTo.add hF_loc (a := 0) (b := x) (c := y) hs0 hx hy
          linarith
        _ = variationOnFromTo F univ x y := by
          rw [variationOnFromTo.eq_of_le _ _ hxy, variationOnFromTo.eq_of_le _ _ hxy, Set.univ_inter]
          have hSet : s ∩ Set.Icc x y = Set.Icc x y := by
            ext z
            constructor
            · intro hz
              exact hz.2
            · intro hz
              exact ⟨⟨hx.1.trans hz.1, hz.2.trans hy.2⟩, hz⟩
          simp [hSet]
    have hF_abs_le {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
        |F y - F x| ≤ V y - V x := by
      -- Endpoint increments are controlled by the variation increment on the same interval.
      rw [hV_diff hx hy hxy, variationOnFromTo.eq_of_le _ _ hxy, Set.univ_inter, ← Real.dist_eq,
        dist_comm, dist_edist]
      apply ENNReal.toReal_mono
      · exact
          (realPrimitive_eVariationOn_Icc_le_intervalIntegral_abs hf hx.1 hxy).trans_lt
            ENNReal.ofReal_lt_top |>.ne
      · exact eVariationOn.edist_le F ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩
    have hV_le {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
        V y - V x ≤ H y - H x := by
      rw [hV_diff hx hy hxy, hH_increment hx.1 hxy]
      simpa [F] using realPrimitive_variationOnFromTo_le_intervalIntegral_abs hf hx.1 hxy
    have hV_sub_mono : MonotoneOn (V - F) s := by
      -- The functions `V - F` and `V + F` are increasing on `[0, t]`.
      intro x hx y hy hxy
      have habs := hF_abs_le hx hy hxy
      have hle : F y - F x ≤ V y - V x := (le_abs_self _).trans habs
      change V x - F x ≤ V y - F y
      linarith
    have hV_add_mono : MonotoneOn (V + F) s := by
      intro x hx y hy hxy
      have habs := hF_abs_le hx hy hxy
      have hle : -(F y - F x) ≤ V y - V x := (neg_le_abs _).trans habs
      change V x + F x ≤ V y + F y
      linarith
    have hHV_mono : MonotoneOn (H - V) s := by
      intro x hx y hy hxy
      have hle := hV_le hx hy hxy
      change H x - V x ≤ H y - V y
      linarith
    have hDeriv_eq :
        ∀ᵐ x, x ∈ s → deriv V x = |f x| := by
      -- Differentiate the three monotone functions on `[0, t]` and squeeze `deriv V`.
      filter_upwards [hV_ac.ae_differentiableAt, hInt.ae_hasDerivAt_integral,
        hIntAbs.ae_hasDerivAt_integral] with x hxV hxF hxH hxmem
      have hsx : x ∈ s := hxmem
      have hUd : UniqueDiffWithinAt ℝ s x := (uniqueDiffOn_Icc htpos x hsx)
      have hV_within : HasDerivWithinAt V (deriv V x) s x :=
        (hxV (by simpa [s, uIcc_of_le ht] using hsx)).hasDerivAt.hasDerivWithinAt
      have hF_at : HasDerivAt F (f x) x := by
        simpa [F, uIcc_of_le ht] using hxF (by simpa [s, uIcc_of_le ht] using hsx) 0
          (by simp [uIcc_of_le ht, ht])
      have hH_at : HasDerivAt H (|f x|) x := by
        simpa [H, uIcc_of_le ht] using hxH (by simpa [s, uIcc_of_le ht] using hsx) 0
          (by simp [uIcc_of_le ht, ht])
      have hSub_nonneg : 0 ≤ deriv V x - f x := by
        have hmono := hV_sub_mono.derivWithin_nonneg (x := x)
        have hder :
            derivWithin (V - F) s x = deriv V x - f x := by
          exact (hV_within.sub hF_at.hasDerivWithinAt).derivWithin hUd
        simpa [hder] using hmono
      have hAdd_nonneg : 0 ≤ deriv V x + f x := by
        have hmono := hV_add_mono.derivWithin_nonneg (x := x)
        have hder :
            derivWithin (V + F) s x = deriv V x + f x := by
          exact (hV_within.add hF_at.hasDerivWithinAt).derivWithin hUd
        simpa [hder] using hmono
      have hTop_nonneg : 0 ≤ |f x| - deriv V x := by
        have hmono := hHV_mono.derivWithin_nonneg (x := x)
        have hder :
            derivWithin (H - V) s x = |f x| - deriv V x := by
          exact (hH_at.hasDerivWithinAt.sub hV_within).derivWithin hUd
        simpa [hder] using hmono
      have hAbs_le : |f x| ≤ deriv V x := by
        rw [abs_le]
        constructor <;> linarith
      have hTop_le : deriv V x ≤ |f x| := by
        linarith
      exact le_antisymm hTop_le hAbs_le
    have hIntegral_eq :
        ∫ x in (0 : ℝ)..(t : ℝ), deriv V x = ∫ x in (0 : ℝ)..(t : ℝ), |f x| := by
      -- Replace `deriv V` by `|f|` almost everywhere on the interval.
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hDeriv_eq] with x hx hxmem
      exact hx (by simpa [s, uIcc_of_le ht] using (uIoc_subset_uIcc hxmem))
    have hV_zero : V 0 = 0 := by
      -- The anchored variation path starts at zero.
      simpa [V] using variationOnFromTo.self F univ (0 : ℝ)
    -- Rewrite the `NNReal` variation as the real variation path, then use FTC.
    calc
      variationProcess (indefiniteIntegralPath f) t =
          (eVariationOn (indefiniteIntegralPath f) (Set.Icc 0 t)).toReal :=
        variationProcess_eq_toReal_eVariationOn_Icc _ _
      _ = (eVariationOn F (Set.Icc (0 : ℝ) (t : ℝ))).toReal := by
        simpa [F] using congrArg ENNReal.toReal
          (eVariationOn_indefiniteIntegralPath_Icc_eq_realPrimitive hf t)
      _ = V (t : ℝ) := by
        simpa [V] using (variationOnFromTo.eq_of_le F univ ht).symm
      _ = ∫ x in (0 : ℝ)..(t : ℝ), deriv V x := by
        have hFTC := hV_ac.integral_deriv_eq_sub
        linarith
      _ = ∫ x in (0 : ℝ)..(t : ℝ), |f x| := hIntegral_eq

-- Proof sketch: every increment of `G = G⁺ - G⁻` is bounded in absolute value by the sum of the
-- corresponding monotone increments of `G⁺` and `G⁻`; taking the supremum over partitions yields
-- the claimed variation bound.
/-- Remark 21.54 (2): if `G = G⁺ - G⁻` with `G⁺` and `G⁻` continuous monotone increasing, then the
variation increment of `G` on `[s,t]` is bounded by the sum of the increments of `G⁺` and `G⁻`. -/
theorem variationOnFromTo_sub_le_add_of_monotone
    {G Gplus Gminus : PathSpace} (hG : G = Gplus - Gminus) (hGplus_mono : Monotone Gplus)
    (hGminus_mono : Monotone Gminus) {s t : NNReal} (hst : s ≤ t) :
    variationOnFromTo G univ s t ≤
      (Gplus t - Gplus s) + (Gminus t - Gminus s) := by
  have hGplus_nonneg : 0 ≤ Gplus t - Gplus s := sub_nonneg_of_le (hGplus_mono hst)
  have hGminus_nonneg : 0 ≤ Gminus t - Gminus s := sub_nonneg_of_le (hGminus_mono hst)
  -- Rewrite the signed variation to total variation on `[s,t]` and transport the interval bound.
  rw [variationOnFromTo.eq_of_le G univ hst, Set.univ_inter]
  calc
    (eVariationOn G (Icc s t)).toReal ≤
        (ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (eVariationOn_Icc_sub_le_of_monotone hG hGplus_mono hGminus_mono hst)
    _ = (Gplus t - Gplus s) + (Gminus t - Gminus s) := by
      simp [add_nonneg hGplus_nonneg hGminus_nonneg]

-- Proof sketch: `G⁺` and `G⁻` are monotone on `univ`, hence each has locally bounded variation;
-- the interval estimate in `variationOnFromTo_sub_le_add_of_monotone` then yields the same
-- property for `G`.
/-- A difference of two continuous monotone increasing paths has locally bounded variation on
`[0, ∞)`. -/
theorem locallyBoundedVariationOn_univ_of_sub_monotone
    {G Gplus Gminus : PathSpace} (hG : G = Gplus - Gminus) (hGplus_mono : Monotone Gplus)
    (hGminus_mono : Monotone Gminus) :
    LocallyBoundedVariationOn G univ := by
  -- The interval estimate above gives finite variation on every initial interval `[0, t]`.
  rw [locallyBoundedVariationOn_univ_iff_forall_boundedVariationOn_Icc_zero]
  intro t
  have hbound :=
    eVariationOn_Icc_sub_le_of_monotone hG hGplus_mono hGminus_mono (s := 0) (t := t) bot_le
  exact (hbound.trans_lt ENNReal.ofReal_lt_top).ne

-- Proof sketch: for a path of locally bounded variation, `variationProcess G` is monotone, and
-- the classical inequalities `-V_t^1(G) ≤ G_t ≤ V_t^1(G)` imply that `(V_t^1(G) ± G_t)/2`
-- inherit monotonicity.
/-- Third part of Remark 21.54: if `G` has locally bounded variation on `[0, ∞)`, then the canonical
Jordan-variation parts
`G_t^+ = (V_t^1(G) + G_t)/2` and `G_t^- = (V_t^1(G) - G_t)/2` are monotone increasing. -/
theorem monotone_positive_and_negative_variationParts_of_locallyBoundedVariationOn
    {G : PathSpace} (hG : LocallyBoundedVariationOn G univ) :
    Monotone (positiveVariationPart G) ∧ Monotone (negativeVariationPart G) := by
  constructor
  · intro s t hst
    -- The positive part gains at least as much as the path can decrease on `[s, t]`.
    have hvar :
        variationProcess G t = variationProcess G s + variationOnFromTo G univ s t := by
      symm
      simpa [variationProcess] using
        (variationOnFromTo.add hG (a := 0) (b := s) (c := t)
          (mem_univ _) (mem_univ _) (mem_univ _))
    have hincr :
        G s - G t ≤ variationOnFromTo G univ s t := by
      calc
        G s - G t = -(G t - G s) := by ring
        _ ≤ |G t - G s| := neg_le_abs _
        _ ≤ variationOnFromTo G univ s t :=
          abs_sub_le_variationOnFromTo_of_locallyBoundedVariation hG hst
    -- After rewriting the variation increment, the remaining arithmetic is linear.
    rw [positiveVariationPart, positiveVariationPart]
    rw [hvar]
    linarith
  · intro s t hst
    -- The negative part gains at least as much as the path can increase on `[s, t]`.
    have hvar :
        variationProcess G t = variationProcess G s + variationOnFromTo G univ s t := by
      symm
      simpa [variationProcess] using
        (variationOnFromTo.add hG (a := 0) (b := s) (c := t)
          (mem_univ _) (mem_univ _) (mem_univ _))
    have hincr :
        G t - G s ≤ variationOnFromTo G univ s t := by
      calc
        G t - G s ≤ |G t - G s| := le_abs_self _
        _ ≤ variationOnFromTo G univ s t :=
          abs_sub_le_variationOnFromTo_of_locallyBoundedVariation hG hst
    -- After rewriting the variation increment, the remaining arithmetic is linear.
    rw [negativeVariationPart, negativeVariationPart]
    rw [hvar]
    linarith

-- Proof sketch: expand the definitions of `positiveVariationPart` and `negativeVariationPart`; the
-- `variationProcess` terms cancel algebraically.
/-- The positive and negative variation parts reconstruct the original path by subtraction. -/
theorem positiveVariationPart_sub_negativeVariationPart (G : PathSpace) :
    positiveVariationPart G - negativeVariationPart G = G := by
  ext t
  -- Expanding the definitions makes the variation terms cancel directly.
  simp [positiveVariationPart, negativeVariationPart]
  ring

/-- Unfolding `signedLebesgueStieltjesIntegralUpTo` gives the Jordan-decomposition formula for the
signed Lebesgue--Stieltjes integral on `[0,t]`. -/
theorem signedLebesgueStieltjesIntegralUpTo_eq
    (F : ℝ → ℝ) (μ : SignedMeasure ℝ) (t : NNReal) :
    signedLebesgueStieltjesIntegralUpTo F μ t =
      ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.posPart -
        ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.negPart :=
  rfl
