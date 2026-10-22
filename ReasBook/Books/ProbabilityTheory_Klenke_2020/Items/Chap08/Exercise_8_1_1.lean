/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open Set
open Filter
open scoped ENNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

/-- Helper for Exercise 8.1.1: the exponential tail above a nonnegative threshold is
`exp (-(θ * t))`. -/
private lemma expMeasure_Ioi_eq_exp_of_nonneg {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    expMeasure θ (Ioi t) = ENNReal.ofReal (Real.exp (-(θ * t))) := by
  -- Proof comment: compute the tail as the complement of the cdf on `Iic t`.
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hIic :
      (expMeasure θ).real (Iic t) = 1 - Real.exp (-(θ * t)) := by
    rw [← cdf_eq_real (μ := expMeasure θ) t, cdf_expMeasure_eq hθ t, if_pos ht]
  have hTailReal :
      (expMeasure θ).real (Ioi t) = Real.exp (-(θ * t)) := by
    calc
      (expMeasure θ).real (Ioi t) = 1 - (expMeasure θ).real (Iic t) := by
        simpa using
          (probReal_compl_eq_one_sub (μ := expMeasure θ) (s := Iic t) measurableSet_Iic)
      _ = Real.exp (-(θ * t)) := by rw [hIic]; ring
  calc
    expMeasure θ (Ioi t) = ENNReal.ofReal ((expMeasure θ).real (Ioi t)) := by
      symm
      exact MeasureTheory.ofReal_measureReal (μ := expMeasure θ) (s := Ioi t)
    _ = ENNReal.ofReal (Real.exp (-(θ * t))) := by rw [hTailReal]

/-- Helper for Exercise 8.1.1: a nonnegative tail identity determines the whole pushforward law
by comparing cdfs on the positive and negative half-lines. -/
private lemma hasLaw_expMeasure_of_tail_eq_on_nonneg
    {θ : ℝ} (hθ : 0 < θ) (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω)
    (hTailEq : ∀ t : ℝ, 0 ≤ t → P (X ⁻¹' Ioi t) = expMeasure θ (Ioi t)) :
    HasLaw X (expMeasure θ) P := by
  -- Proof comment: push `X` forward to a measure on `ℝ` and recover it from its cdf.
  refine ⟨hX_meas.aemeasurable, ?_⟩
  let μ : Measure ℝ := Measure.map X P
  letI : IsProbabilityMeasure μ :=
    MeasureTheory.Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hIoi_zero_one : P (X ⁻¹' Ioi (0 : ℝ)) = 1 := by
    exact (MeasureTheory.ae_iff_prob_eq_one (μ := P) (p := fun ω ↦ 0 < X ω)
      (measurable_const.lt hX_meas)).1 hX_pos
  have hCdfEq : cdf μ = cdf (expMeasure θ) := by
    ext x
    by_cases hx : 0 ≤ x
    · -- Proof comment: on `x ≥ 0`, the assumed tail formula determines the cdf directly.
      have hTailReal : μ.real (Ioi x) = Real.exp (-(θ * x)) := by
        calc
          μ.real (Ioi x) = (μ (Ioi x)).toReal := by rw [MeasureTheory.Measure.real_def]
          _ = (expMeasure θ (Ioi x)).toReal := by
            rw [show μ (Ioi x) = P (X ⁻¹' Ioi x) by
              rw [MeasureTheory.Measure.map_apply hX_meas measurableSet_Ioi]]
            rw [hTailEq x hx]
          _ = Real.exp (-(θ * x)) := by
            rw [expMeasure_Ioi_eq_exp_of_nonneg hθ hx, ENNReal.toReal_ofReal]
            positivity
      have hComp : μ.real (Ioi x) = 1 - μ.real (Iic x) := by
        simpa using
          (MeasureTheory.probReal_compl_eq_one_sub (μ := μ) (s := Iic x) measurableSet_Iic)
      have hIicReal : μ.real (Iic x) = 1 - Real.exp (-(θ * x)) := by
        linarith
      calc
        (cdf μ) x = μ.real (Iic x) := by rw [cdf_eq_real]
        _ = 1 - Real.exp (-(θ * x)) := hIicReal
        _ = (cdf (expMeasure θ)) x := by
          rw [cdf_expMeasure_eq hθ x, if_pos hx]
    · -- Proof comment: on `x < 0`, strict positivity of `X` forces the cdf to vanish.
      have hx' : x < 0 := lt_of_not_ge hx
      have hIic_zero_zero : μ (Iic (0 : ℝ)) = 0 := by
        have hTailZero : μ (Ioi (0 : ℝ)) = 1 := by
          rw [show μ (Ioi (0 : ℝ)) = P (X ⁻¹' Ioi (0 : ℝ)) by
            rw [MeasureTheory.Measure.map_apply hX_meas measurableSet_Ioi]]
          exact hIoi_zero_one
        simpa using
          (MeasureTheory.prob_compl_eq_zero_iff (μ := μ) (s := Ioi (0 : ℝ))
            measurableSet_Ioi).2 hTailZero
      have hIic_zero : μ (Iic x) = 0 := by
        refine MeasureTheory.measure_mono_null (μ := μ) ?_ hIic_zero_zero
        intro y hy
        exact le_trans hy hx'.le
      calc
        (cdf μ) x = μ.real (Iic x) := by rw [cdf_eq_real]
        _ = 0 := by rw [MeasureTheory.Measure.real_def, hIic_zero, ENNReal.toReal_zero]
        _ = (cdf (expMeasure θ)) x := by
          rw [cdf_expMeasure_eq hθ x, if_neg hx]
  have hMapEq : μ = expMeasure θ :=
    (MeasureTheory.Measure.cdf_eq_iff μ (expMeasure θ)).1 hCdfEq
  simpa [μ] using hMapEq

/-- Helper for Exercise 8.1.1: a multiplicative survival function on `ℝ≥0` is strictly positive
everywhere once one positive tail value is known. -/
private lemma survivalFunctionPos_of_memoryless {S : ℝ → ℝ}
    (hZero : S 0 = 1)
    (hNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ S t)
    (hAnti : AntitoneOn S (Set.Ici 0))
    (hMul : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hSmall : ∃ u > 0, 0 < S u) :
    ∀ t : ℝ, 0 ≤ t → 0 < S t := by
  intro t ht
  rcases hSmall with ⟨u, hu, hSu⟩
  by_cases ht0 : t = 0
  · -- Proof comment: the origin is normalized by `S 0 = 1`.
    subst ht0
    simp [hZero]
  · -- Proof comment: subdivide `t` into many smaller pieces and compare one piece with `u`.
    by_contra hSt
    have hSt' : S t = 0 := by
      have hSt_nonneg : 0 ≤ S t := hNonneg t ht
      linarith
    obtain ⟨n, hn_gt⟩ : ∃ n : ℕ, t / u < n := exists_nat_gt (t / u)
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      subst hn0
      have : 0 < t / u := by positivity
      linarith
    have hn_nat : 0 < n := Nat.pos_of_ne_zero hn_ne_zero
    have hn : 0 < (n : ℝ) := by exact_mod_cast hn_nat
    let a : ℝ := t / n
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      positivity
    have ha_le_u : a ≤ u := by
      have htu : t < (n : ℝ) * u := by
        exact (div_lt_iff₀ hu).mp hn_gt
      exact (div_le_iff₀ hn).2 <| by simpa [mul_comm] using htu.le
    have hPow :
        ∀ m : ℕ, S ((m : ℝ) * a) = (S a) ^ m := by
      intro m
      induction m with
      | zero =>
          simp [hZero]
      | succ m hm =>
          have hSucc : ((Nat.succ m : ℝ) * a) = (m : ℝ) * a + a := by
            norm_num [Nat.succ_eq_add_one, add_mul]
          calc
            S ((Nat.succ m : ℝ) * a) = S ((m : ℝ) * a + a) := by rw [hSucc]
            _ = S ((m : ℝ) * a) * S a := by
              rw [hMul ((m : ℝ) * a) a (by positivity) ha_nonneg]
            _ = (S a) ^ m * S a := by rw [hm]
            _ = (S a) ^ Nat.succ m := by rw [pow_succ, mul_comm]
    have ht_eq : t = (n : ℝ) * a := by
      dsimp [a]
      field_simp [hn_ne_zero]
    have hSa_zero : S a = 0 := by
      have hPowZero : (S a) ^ n = 0 := by
        rw [← hPow n, ← ht_eq, hSt']
      exact eq_zero_of_pow_eq_zero hPowZero
    have hLe : S u ≤ S a := hAnti (by simpa using ha_nonneg) (by simpa using hu.le) ha_le_u
    have : S u ≤ 0 := by simpa [hSa_zero] using hLe
    linarith

/-- Helper for Exercise 8.1.1: additivity on `ℝ≥0` rewrites subtraction inside the domain. -/
private lemma nonnegAdditive_sub_eq {F : ℝ → ℝ}
    (hAdd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → F (s + t) = F s + F t)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    F (t - s) = F t - F s := by
  -- Proof comment: compare `F t` with `F ((t - s) + s)` and solve the resulting linear identity.
  have hsum : F ((t - s) + s) = F (t - s) + F s := by
    exact hAdd (t - s) s (sub_nonneg.2 hst) hs
  have hEq : F t = F (t - s) + F s := by simpa [sub_add_cancel] using hsum
  linarith

/-- Helper for Exercise 8.1.1: extend a nonnegative additive function to an additive hom on all
of `ℝ` by odd reflection. -/
private lemma nonnegAdditive_toAddMonoidHom {F : ℝ → ℝ}
    (hZero : F 0 = 0)
    (hAdd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → F (s + t) = F s + F t) :
    ∃ G : ℝ →+ ℝ, ∀ t : ℝ, 0 ≤ t → G t = F t := by
  -- Proof comment: reflect `F` oddly across the origin and check additivity by sign cases.
  let Gfun : ℝ → ℝ := fun x ↦ if 0 ≤ x then F x else -F (-x)
  have hG_add : ∀ x y : ℝ, Gfun (x + y) = Gfun x + Gfun y := by
    intro x y
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · have hxy : 0 ≤ x + y := add_nonneg hx hy
        simp [Gfun, hxy, hx, hy, hAdd x y hx hy]
      · by_cases hxy : 0 ≤ x + y
        · have hneg_y : 0 ≤ -y := by linarith
          have hneg_y_le_x : -y ≤ x := by linarith
          calc
            Gfun (x + y) = F (x + y) := by simp [Gfun, hxy]
            _ = F (x - (-y)) := by congr 1; ring
            _ = F x - F (-y) := by
              rw [nonnegAdditive_sub_eq hAdd hneg_y hneg_y_le_x]
            _ = Gfun x + Gfun y := by
              simp [Gfun, hx, hy]
              ring
        · have hneg_y : 0 ≤ -y := by linarith
          have hx_le_neg_y : x ≤ -y := by linarith
          calc
            Gfun (x + y) = -F (-(x + y)) := by simp [Gfun, hxy]
            _ = -F ((-y) - x) := by congr 1; ring
            _ = -(F (-y) - F x) := by
              rw [nonnegAdditive_sub_eq hAdd hx hx_le_neg_y]
            _ = Gfun x + Gfun y := by
              simp [Gfun, hx, hy]
              ring
    · by_cases hy : 0 ≤ y
      · by_cases hxy : 0 ≤ x + y
        · have hneg_x : 0 ≤ -x := by linarith
          have hneg_x_le_y : -x ≤ y := by linarith
          calc
            Gfun (x + y) = F (x + y) := by simp [Gfun, hxy]
            _ = F (y - (-x)) := by congr 1; ring
            _ = F y - F (-x) := by
              rw [nonnegAdditive_sub_eq hAdd hneg_x hneg_x_le_y]
            _ = Gfun x + Gfun y := by
              simp [Gfun, hx, hy]
              ring
        · have hneg_x : 0 ≤ -x := by linarith
          have hy_le_neg_x : y ≤ -x := by linarith
          calc
            Gfun (x + y) = -F (-(x + y)) := by simp [Gfun, hxy]
            _ = -F ((-x) - y) := by congr 1; ring
            _ = -(F (-x) - F y) := by
              rw [nonnegAdditive_sub_eq hAdd hy hy_le_neg_x]
            _ = Gfun x + Gfun y := by
              simp [Gfun, hx, hy]
              ring
      · have hxy : ¬ 0 ≤ x + y := by linarith
        have hneg_x : 0 ≤ -x := by linarith
        have hneg_y : 0 ≤ -y := by linarith
        calc
          Gfun (x + y) = -F (-(x + y)) := by simp [Gfun, hxy]
          _ = -F ((-x) + (-y)) := by congr 1; ring
          _ = -(F (-x) + F (-y)) := by rw [hAdd (-x) (-y) hneg_x hneg_y]
          _ = Gfun x + Gfun y := by
            simp [Gfun, hx, hy]
            ring
  refine ⟨
    { toFun := Gfun
      map_zero' := by simp [Gfun, hZero]
      map_add' := hG_add }, ?_⟩
  intro t ht
  simp [Gfun, ht]

/-- Helper for Exercise 8.1.1: a monotone additive function on `ℝ≥0` is determined by its value
at `1`. -/
private lemma monotoneAdditiveOn_nonneg_eq_mul {F : ℝ → ℝ}
    (hZero : F 0 = 0)
    (hAdd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → F (s + t) = F s + F t)
    (hMono : MonotoneOn F (Set.Ici 0)) :
    ∀ t : ℝ, 0 ≤ t → F t = t * F 1 := by
  -- Route correction: replace the stalled rational-mesh argument by an additive-hom extension to
  -- all of `ℝ`, then invoke measurability, continuity, and real-linearity from mathlib.
  rcases nonnegAdditive_toAddMonoidHom hZero hAdd with ⟨G, hG_eq⟩
  have hG_nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ G x := by
    intro x hx
    have hFx_ge : F 0 ≤ F x := hMono (by simp) (by simpa using hx) hx
    rw [hG_eq x hx]
    simpa [hZero] using hFx_ge
  have hG_mono : Monotone (G : ℝ → ℝ) := (monotone_iff_map_nonneg G).2 hG_nonneg
  have hG_meas : Measurable G := hG_mono.measurable
  have ⟨s, hs, hs_bdd⟩ := G.exists_nhds_isBounded hG_meas 0
  have hG_cont : Continuous G := G.continuous_of_isBounded_nhds_zero hs hs_bdd
  let L : ℝ →L[ℝ] ℝ := G.toRealLinearMap hG_cont
  have hG_linear : ∀ x : ℝ, G x = x * G 1 := by
    intro x
    simpa [L, smul_eq_mul] using (L.map_smul x (1 : ℝ))
  intro t ht
  -- Proof comment: compare `F` with its additive extension on the nonnegative half-line.
  calc
    F t = G t := by symm; exact hG_eq t ht
    _ = t * G 1 := hG_linear t
    _ = t * F 1 := by rw [hG_eq 1 zero_le_one]

/-- Helper for Exercise 8.1.1: a positive, antitone, multiplicative survival function on
`ℝ≥0` with tail limit `0` is an exponential tail. -/
private lemma memorylessSurvival_eq_exp {S : ℝ → ℝ}
    (hZero : S 0 = 1)
    (hPos : ∀ t : ℝ, 0 ≤ t → 0 < S t)
    (hMul : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hAnti : AntitoneOn S (Set.Ici 0))
    (hLimit : Tendsto S atTop (𝓝 0)) :
    ∃ θ > 0, ∀ t : ℝ, 0 ≤ t → S t = Real.exp (-(θ * t)) := by
  let F : ℝ → ℝ := fun t ↦ -Real.log (S t)
  have hF_zero : F 0 = 0 := by
    -- Proof comment: the logarithmic normalization preserves the origin.
    rw [show F 0 = -Real.log (S 0) by rfl, hZero, Real.log_one, neg_zero]
  have hF_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → F (s + t) = F s + F t := by
    intro s t hs ht
    -- Proof comment: the multiplicative tail law becomes additivity after taking `-log`.
    rw [show F (s + t) = -Real.log (S (s + t)) by rfl]
    rw [hMul s t hs ht, Real.log_mul (ne_of_gt (hPos s hs)) (ne_of_gt (hPos t ht))]
    ring
  have hF_mono : MonotoneOn F (Set.Ici 0) := by
    intro a ha b hb hab
    -- Proof comment: `S` is antitone, so `-log ∘ S` is monotone on positive inputs.
    have hSb_le_hSa : S b ≤ S a := hAnti ha hb hab
    have hlog : Real.log (S b) ≤ Real.log (S a) := Real.log_le_log (hPos b hb) hSb_le_hSa
    linarith
  have hF_linear := monotoneAdditiveOn_nonneg_eq_mul hF_zero hF_add hF_mono
  have hS1_pos : 0 < S 1 := hPos 1 zero_le_one
  have hS1_le_one : S 1 ≤ 1 := by
    have hStep : S 1 ≤ S 0 := hAnti (by simp) (by simp) zero_le_one
    simpa [hZero] using hStep
  have hS1_lt_one : S 1 < 1 := by
    by_contra hNot
    have hS1_eq : S 1 = 1 := le_antisymm hS1_le_one (not_lt.mp hNot)
    have hNatOne : ∀ n : ℕ, S (n : ℝ) = 1 := by
      intro n
      induction n with
      | zero =>
          simpa using hZero
      | succ n ih =>
          calc
            S ((Nat.succ n : ℕ) : ℝ) = S ((n : ℝ) + 1) := by norm_num
            _ = S (n : ℝ) * S 1 := by
              rw [hMul (n : ℝ) 1 (by exact_mod_cast Nat.zero_le n) zero_le_one]
            _ = 1 := by simp [ih, hS1_eq]
    have hNatLimit : Tendsto (fun n : ℕ ↦ S (n : ℝ)) atTop (𝓝 0) := by
      simpa using hLimit.comp tendsto_natCast_atTop_atTop
    have hConstLimit : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) := by
      convert hNatLimit using 1
      ext n
      simp [hNatOne]
    have : (1 : ℝ) = 0 := (tendsto_const_nhds_iff).1 hConstLimit
    norm_num at this
  let θ : ℝ := F 1
  refine ⟨θ, ?_, ?_⟩
  · -- Proof comment: the tail at `1` lies strictly between `0` and `1`, so its log is negative.
    dsimp [θ, F]
    exact neg_pos.mpr (Real.log_neg hS1_pos hS1_lt_one)
  · intro t ht
    have hFt : F t = t * θ := by
      simpa [θ] using hF_linear t ht
    have hLog : Real.log (S t) = -(θ * t) := by
      rw [mul_comm t θ] at hFt
      dsimp [F] at hFt
      linarith
    -- Proof comment: exponentiate the linearized logarithm to recover the tail itself.
    calc
      S t = Real.exp (Real.log (S t)) := by rw [Real.exp_log (hPos t ht)]
      _ = Real.exp (-(θ * t)) := by rw [hLog]

/-- Helper for Exercise 8.1.1: a strictly positive random variable with a memoryless tail should
be identified by classifying the pushforward survival function as an exponential. -/
private lemma memorylessTail_hasLaw_expMeasure
    (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω)
    (hTail : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      P (X ⁻¹' Ioi (t + s)) = P (X ⁻¹' Ioi t) * P (X ⁻¹' Ioi s)) :
    ∃ θ > 0, HasLaw X (expMeasure θ) P := by
  -- Route correction: classify the pushforward tail locally and finish with the extracted cdf
  -- comparison helper instead of relying on the later fixed-rate theorem.
  let μ : Measure ℝ := Measure.map X P
  letI : IsProbabilityMeasure μ :=
    MeasureTheory.Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  let S : ℝ → ℝ := fun t ↦ μ.real (Ioi t)
  have hMapIoi : ∀ t : ℝ, μ (Ioi t) = P (X ⁻¹' Ioi t) := by
    intro t
    simpa [μ] using
      (MeasureTheory.Measure.map_apply (μ := P) (f := X) hX_meas measurableSet_Ioi
        (s := Ioi t))
  have hIoi_zero_one : P (X ⁻¹' Ioi (0 : ℝ)) = 1 := by
    exact (MeasureTheory.ae_iff_prob_eq_one (μ := P) (p := fun ω ↦ 0 < X ω)
      (measurable_const.lt hX_meas)).1 hX_pos
  have hZero : S 0 = 1 := by
    simp [S, MeasureTheory.Measure.real_def, hMapIoi 0, hIoi_zero_one]
  have hNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ S t := by
    intro t ht
    simp [S, MeasureTheory.Measure.real_def]
  have hAnti : AntitoneOn S (Set.Ici 0) := by
    intro x hx y hy hxy
    have hIoi_mono : μ (Ioi y) ≤ μ (Ioi x) := MeasureTheory.measure_mono (Ioi_subset_Ioi hxy)
    simpa [S, MeasureTheory.Measure.real_def] using
      (ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ _) hIoi_mono :
        (μ (Ioi y)).toReal ≤ (μ (Ioi x)).toReal)
  have hMulS : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t := by
    intro s t hs ht
    have hTailEq :
        μ (Ioi (s + t)) = μ (Ioi s) * μ (Ioi t) := by
      rw [hMapIoi (s + t), hMapIoi s, hMapIoi t, hTail t s ht hs, mul_comm]
    exact (by
      simpa [S, MeasureTheory.Measure.real_def, ENNReal.toReal_mul] using
        congrArg ENNReal.toReal hTailEq)
  have hSmall : ∃ u > 0, 0 < S u := by
    have hUnion :
        X ⁻¹' Ioi (0 : ℝ) = ⋃ n : ℕ, X ⁻¹' Ioi (1 / (n + 1 : ℝ)) := by
      ext ω
      constructor
      · intro hω
        have hω_pos : 0 < X ω := hω
        rcases exists_nat_one_div_lt hω_pos with ⟨n, hn⟩
        exact mem_iUnion.2 ⟨n, hn⟩
      · intro hω
        rcases mem_iUnion.1 hω with ⟨n, hn⟩
        exact lt_trans (by positivity : 0 < 1 / (n + 1 : ℝ)) hn
    by_contra hNo
    have hEachZero : ∀ n : ℕ, P (X ⁻¹' Ioi (1 / (n + 1 : ℝ))) = 0 := by
      intro n
      by_contra hn
      have hTailPos : 0 < S (1 / (n + 1 : ℝ)) := by
        have hMeasureNeZero : μ (Ioi (1 / (n + 1 : ℝ))) ≠ 0 := by
          rw [hMapIoi (1 / (n + 1 : ℝ))]
          exact hn
        simpa [S, MeasureTheory.Measure.real_def] using
          (ENNReal.toReal_pos hMeasureNeZero (MeasureTheory.measure_ne_top μ _))
      exact hNo ⟨1 / (n + 1 : ℝ), by positivity, hTailPos⟩
    have hUnionZero : P (⋃ n : ℕ, X ⁻¹' Ioi (1 / (n + 1 : ℝ))) = 0 := by
      exact MeasureTheory.measure_iUnion_null hEachZero
    have hUnionOne : P (⋃ n : ℕ, X ⁻¹' Ioi (1 / (n + 1 : ℝ))) = 1 := by
      simpa [hUnion] using hIoi_zero_one
    rw [hUnionZero] at hUnionOne
    norm_num at hUnionOne
  have hPosS : ∀ t : ℝ, 0 ≤ t → 0 < S t :=
    survivalFunctionPos_of_memoryless hZero hNonneg hAnti hMulS hSmall
  have hLimitS : Tendsto S atTop (𝓝 0) := by
    have hTailReal : ∀ t : ℝ, S t = 1 - cdf μ t := by
      intro t
      simpa [S, ProbabilityTheory.cdf_eq_real (μ := μ)] using
        (MeasureTheory.probReal_compl_eq_one_sub (μ := μ) (s := Iic t) measurableSet_Iic)
    have hOneMinus :
        Tendsto (fun t : ℝ ↦ 1 - cdf μ t) atTop (𝓝 0) := by
      have hOne : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa using hOne.sub (ProbabilityTheory.tendsto_cdf_atTop (μ := μ))
    have hTailRealFun : S = fun t : ℝ ↦ 1 - cdf μ t := by
      funext t
      exact hTailReal t
    simpa [hTailRealFun] using hOneMinus
  rcases memorylessSurvival_eq_exp hZero hPosS hMulS hAnti hLimitS with ⟨θ, hθ, hExp⟩
  refine ⟨θ, hθ, ?_⟩
  have hTailEq : ∀ t : ℝ, 0 ≤ t → P (X ⁻¹' Ioi t) = expMeasure θ (Ioi t) := by
    intro t ht
    calc
      P (X ⁻¹' Ioi t) = μ (Ioi t) := by rw [← hMapIoi t]
      _ = ENNReal.ofReal (S t) := by
        change μ (Ioi t) = ENNReal.ofReal (μ.real (Ioi t))
        exact (MeasureTheory.ofReal_measureReal (μ := μ) (s := Ioi t)).symm
      _ = ENNReal.ofReal (Real.exp (-(θ * t))) := by rw [hExp t ht]
      _ = expMeasure θ (Ioi t) := by rw [expMeasure_Ioi_eq_exp_of_nonneg hθ ht]
  exact hasLaw_expMeasure_of_tail_eq_on_nonneg hθ hX_meas hX_pos hTailEq

-- Proof sketch: for the forward implication, use `cdf_expMeasure_eq` to identify the survival
-- function of `expMeasure θ` as `exp (-θ t)` and then derive the multiplicative tail identity
-- `P[X > t + s] = P[X > t] * P[X > s]`. For the reverse implication, show that this tail identity
-- forces the survival function `t ↦ P {ω | t < X ω}` to solve the multiplicative Cauchy equation
-- on `ℝ≥0`; positivity and measurability then identify it with `exp (-θ t)` for some `θ > 0`,
-- yielding `HasLaw X (expMeasure θ) P`.
/-- Exercise 8.1.1: a strictly positive real random variable on a probability space is
exponentially distributed for some rate if and only if its tail probabilities are memoryless,
equivalently `P[X > t + s] = P[X > t] * P[X > s]` for all `s, t ≥ 0`. -/
theorem strictly_positive_has_exponential_law_iff_memoryless
    (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    (∃ θ > 0, HasLaw X (expMeasure θ) P) ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) = P (X ⁻¹' Ioi t) * P (X ⁻¹' Ioi s) := by
  constructor
  · rintro ⟨θ, hθ, hLaw⟩ s t hs ht
    -- Proof comment: transport the three tail events through the pushforward law of `X`.
    have hPreimage :
        ∀ r : ℝ, P (X ⁻¹' Ioi r) = expMeasure θ (Ioi r) := by
      intro r
      calc
        P (X ⁻¹' Ioi r) = Measure.map X P (Ioi r) := by
          rw [MeasureTheory.Measure.map_apply hX_meas measurableSet_Ioi]
        _ = expMeasure θ (Ioi r) := by rw [hLaw.map_eq]
    calc
      P (X ⁻¹' Ioi (t + s)) = expMeasure θ (Ioi (t + s)) := hPreimage (t + s)
      _ = ENNReal.ofReal (Real.exp (-(θ * (t + s)))) := by
        rw [expMeasure_Ioi_eq_exp_of_nonneg hθ (add_nonneg ht hs)]
      _ =
          ENNReal.ofReal (Real.exp (-(θ * t))) *
            ENNReal.ofReal (Real.exp (-(θ * s))) := by
          rw [← ENNReal.ofReal_mul (show 0 ≤ Real.exp (-(θ * t)) by positivity)]
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
      _ = expMeasure θ (Ioi t) * expMeasure θ (Ioi s) := by
        rw [← expMeasure_Ioi_eq_exp_of_nonneg hθ ht, ← expMeasure_Ioi_eq_exp_of_nonneg hθ hs]
      _ = P (X ⁻¹' Ioi t) * P (X ⁻¹' Ioi s) := by rw [← hPreimage t, ← hPreimage s]
  · intro hTail
    -- Proof comment: the remaining work is the survival-function classification encoded in the
    -- dedicated helper above.
    exact memorylessTail_hasLaw_expMeasure hX_meas hX_pos hTail

-- Proof sketch: rewrite the law statement as the fixed-rate multiplicative tail identity
-- `P[X > t + s] = expMeasure θ (Ioi t) * P[X > s]`. This keeps the main characterization in
-- canonical `HasLaw`/measure form and avoids conditioning on null tail events.
/-- A strictly positive real random variable has law `expMeasure θ` with `θ > 0` exactly when its
tail probabilities satisfy the fixed-rate memoryless identity
`P[X > t + s] = expMeasure θ (Ioi t) * P[X > s]` for all `s, t ≥ 0`. -/
theorem hasLaw_expMeasure_iff_tail_eq_expMeasure_tail_mul_tail
    {θ : ℝ} (hθ : 0 < θ) (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    HasLaw X (expMeasure θ) P ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) = expMeasure θ (Ioi t) * P (X ⁻¹' Ioi s) := by
  constructor
  · intro hLaw s t hs ht
    -- Proof comment: rewrite both tail events through the pushforward law of `X`.
    have hPreimage :
        ∀ r : ℝ, P (X ⁻¹' Ioi r) = expMeasure θ (Ioi r) := by
      intro r
      calc
        P (X ⁻¹' Ioi r) = Measure.map X P (Ioi r) := by
          rw [MeasureTheory.Measure.map_apply hX_meas measurableSet_Ioi]
        _ = expMeasure θ (Ioi r) := by rw [hLaw.map_eq]
    calc
      P (X ⁻¹' Ioi (t + s)) = expMeasure θ (Ioi (t + s)) := hPreimage (t + s)
      _ = ENNReal.ofReal (Real.exp (-(θ * (t + s)))) := by
        rw [expMeasure_Ioi_eq_exp_of_nonneg hθ (add_nonneg ht hs)]
      _ =
          ENNReal.ofReal (Real.exp (-(θ * t))) *
            ENNReal.ofReal (Real.exp (-(θ * s))) := by
          rw [← ENNReal.ofReal_mul (show 0 ≤ Real.exp (-(θ * t)) by positivity)]
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
      _ = expMeasure θ (Ioi t) * expMeasure θ (Ioi s) := by
        rw [← expMeasure_Ioi_eq_exp_of_nonneg hθ ht, ← expMeasure_Ioi_eq_exp_of_nonneg hθ hs]
      _ = expMeasure θ (Ioi t) * P (X ⁻¹' Ioi s) := by rw [hPreimage s]
  · intro hTail
    -- Proof comment: set `s = 0` to recover the full tail of `Measure.map X P`, then compare cdfs.
    refine ⟨hX_meas.aemeasurable, ?_⟩
    let μ : Measure ℝ := Measure.map X P
    letI : IsProbabilityMeasure μ :=
      MeasureTheory.Measure.isProbabilityMeasure_map hX_meas.aemeasurable
    letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
    have hIoi_zero_one : P (X ⁻¹' Ioi (0 : ℝ)) = 1 := by
      exact (MeasureTheory.ae_iff_prob_eq_one (μ := P) (p := fun ω ↦ 0 < X ω)
        (measurable_const.lt hX_meas)).1 hX_pos
    have hTailEq :
        ∀ t : ℝ, 0 ≤ t → P (X ⁻¹' Ioi t) = expMeasure θ (Ioi t) := by
      intro t ht
      have hStep := hTail 0 t le_rfl ht
      simpa [zero_add, hIoi_zero_one] using hStep
    have hCdfEq : cdf μ = cdf (expMeasure θ) := by
      ext x
      by_cases hx : 0 ≤ x
      · have hTailReal : μ.real (Ioi x) = Real.exp (-(θ * x)) := by
          calc
            μ.real (Ioi x) = (μ (Ioi x)).toReal := by rw [MeasureTheory.Measure.real_def]
            _ = (expMeasure θ (Ioi x)).toReal := by
              rw [show μ (Ioi x) = P (X ⁻¹' Ioi x) by
                rw [MeasureTheory.Measure.map_apply hX_meas measurableSet_Ioi]]
              rw [hTailEq x hx]
            _ = Real.exp (-(θ * x)) := by
              rw [expMeasure_Ioi_eq_exp_of_nonneg hθ hx, ENNReal.toReal_ofReal]
              positivity
        have hComp : μ.real (Ioi x) = 1 - μ.real (Iic x) := by
          simpa using
            (probReal_compl_eq_one_sub (μ := μ) (s := Iic x) measurableSet_Iic)
        have hIicReal : μ.real (Iic x) = 1 - Real.exp (-(θ * x)) := by
          linarith
        calc
          (cdf μ) x = μ.real (Iic x) := by rw [cdf_eq_real]
          _ = 1 - Real.exp (-(θ * x)) := hIicReal
          _ = (cdf (expMeasure θ)) x := by
            rw [cdf_expMeasure_eq hθ x, if_pos hx]
      · have hx' : x < 0 := lt_of_not_ge hx
        have hIic_zero_zero : μ (Iic (0 : ℝ)) = 0 := by
          have hTailZero : μ (Ioi (0 : ℝ)) = 1 := by
            rw [show μ (Ioi (0 : ℝ)) = P (X ⁻¹' Ioi (0 : ℝ)) by
              rw [MeasureTheory.Measure.map_apply hX_meas measurableSet_Ioi]]
            exact hIoi_zero_one
          simpa using
            (MeasureTheory.prob_compl_eq_zero_iff (μ := μ) (s := Ioi (0 : ℝ))
              measurableSet_Ioi).2 hTailZero
        have hIic_zero : μ (Iic x) = 0 := by
          refine MeasureTheory.measure_mono_null (μ := μ) ?_ hIic_zero_zero
          intro y hy
          exact le_trans hy hx'.le
        calc
          (cdf μ) x = μ.real (Iic x) := by rw [cdf_eq_real]
          _ = 0 := by rw [MeasureTheory.Measure.real_def, hIic_zero, ENNReal.toReal_zero]
          _ = (cdf (expMeasure θ)) x := by
            rw [cdf_expMeasure_eq hθ x, if_neg hx]
    have hMapEq : μ = expMeasure θ :=
      (MeasureTheory.Measure.cdf_eq_iff μ (expMeasure θ)).1 hCdfEq
    simpa [μ] using hMapEq

-- Proof sketch: combine the canonical tail characterization with the explicit exponential tail
-- formula `expMeasure θ (Ioi t) = exp (-θ t)` for `t ≥ 0`, obtained from `cdf_expMeasure_eq`.
/-- A strictly positive real random variable has exponential law of rate `θ > 0` exactly when its
tail probabilities satisfy the explicit fixed-rate identity
`P[X > t + s] = exp (-θ t) * P[X > s]` for all `s, t ≥ 0`. -/
theorem hasLaw_expMeasure_iff_tail_eq_exp_mul_tail
    {θ : ℝ} (hθ : 0 < θ) (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    HasLaw X (expMeasure θ) P ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) =
          ENNReal.ofReal (Real.exp (-(θ * t))) * P (X ⁻¹' Ioi s) := by
  constructor
  · intro hLaw s t hs ht
    -- Proof comment: rewrite the canonical fixed-rate factor with the exponential tail formula.
    have hFixed :=
      (hasLaw_expMeasure_iff_tail_eq_expMeasure_tail_mul_tail hθ hX_meas hX_pos).1 hLaw
        s t hs ht
    rw [expMeasure_Ioi_eq_exp_of_nonneg hθ ht] at hFixed
    simpa using hFixed
  · intro hTail
    -- Proof comment: convert the explicit factor back to the canonical `expMeasure` tail.
    refine
      (hasLaw_expMeasure_iff_tail_eq_expMeasure_tail_mul_tail hθ hX_meas hX_pos).2 ?_
    intro s t hs ht
    have hStep := hTail s t hs ht
    rw [expMeasure_Ioi_eq_exp_of_nonneg hθ ht]
    simpa using hStep
