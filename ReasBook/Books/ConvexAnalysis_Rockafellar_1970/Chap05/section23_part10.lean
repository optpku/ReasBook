/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part9

section Chap05
section Section23

open scoped ConvexAnalysis Pointwise

/-- Helper for Theorem 23.10: once a direction stays in the active-constraint cone, a chosen
active affine piece with maximal slope controls every represented difference quotient on a common
small-step interval. -/
lemma helperForTheorem_23_10_directionalDifferenceQuotient_eq_activeSlopeMax_of_mem_activeDirectionCone
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal} {x d : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hdTx :
      d ∈ {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
        (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0})
    {imax : Fin m}
    (himax :
      (imax : ℕ) < k ∧ ((∑ j, x j * b imax j) - β imax) = (f x).toReal)
    (hmax :
      ∀ i : Fin m,
        (i : ℕ) < k →
          ((∑ j, x j * b i j) - β i) = (f x).toReal →
            (∑ j, d j * b i j) ≤ (∑ j, d j * b imax j)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 0 < t → t < ε →
        directionalDifferenceQuotientAt f x d t =
          (((∑ j, d j * b imax j) : ℝ) : EReal) := by
  classical
  let C : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  let Iaff : Finset (Fin m) := Finset.univ.filter fun i : Fin m => (i : ℕ) < k
  let pieceAt : Fin m → (Fin n → ℝ) → ℝ := fun i y => (∑ j, y j * b i j) - β i
  let slope : Fin m → ℝ := fun i => ∑ j, d j * b i j
  have hxC : x ∈ C := by
    -- Finiteness at `x` forces the indicator branch of the representation to vanish.
    simpa [C] using
      helperForTheorem_23_10_finitePoint_mem_domain_of_representation
        (f := f) (x := x) (b := b) (β := β) hrepr hx
  rcases
      helperForTheorem_23_10_activeDirectionCone_smallStep_radius
        (k := k) (b := b) (β := β) (x := x) (d := d) hxC hdTx with
    ⟨εC, hεCpos, hεC⟩
  let radius : Fin m → ℝ := fun i =>
    if hi : (i : ℕ) < k then
      if hactive : pieceAt i x = (f x).toReal then
        1
      else
        Classical.choose
          (helperForTheorem_23_10_inactiveAffine_piece_stays_below_activeSlopeMaximizer
            (f := f) (x := x) (d := d) (b := b) (β := β) (i := i) (imax := imax)
            hrepr hx hi himax hactive)
    else 1
  let radii : Finset ℝ := insert εC (Finset.univ.image radius)
  have hradius_pos : ∀ i : Fin m, 0 < radius i := by
    intro i
    by_cases hi : (i : ℕ) < k
    · by_cases hactive : pieceAt i x = (f x).toReal
      · simp [radius, hi, hactive]
      · have hchosen :=
          Classical.choose_spec
            (helperForTheorem_23_10_inactiveAffine_piece_stays_below_activeSlopeMaximizer
              (f := f) (x := x) (d := d) (b := b) (β := β) (i := i) (imax := imax)
              hrepr hx hi himax hactive)
        simpa [radius, hi, hactive] using hchosen.1
    · simp [radius, hi]
  have hradii_nonempty : radii.Nonempty := by
    simp [radii]
  let ε : ℝ := radii.min' hradii_nonempty
  have hεpos : 0 < ε := by
    have hmem : ε ∈ radii := by
      simpa [ε, radii] using Finset.min'_mem radii hradii_nonempty
    rcases Finset.mem_insert.1 hmem with hεeq | hεimage
    · linarith [hεCpos]
    · rcases Finset.mem_image.1 hεimage with ⟨i, -, hEq⟩
      simpa [ε, hEq] using hradius_pos i
  have hεleC : ε ≤ εC := by
    have hmem : εC ∈ radii := by simp [radii]
    have hmin_le : radii.min' hradii_nonempty ≤ εC :=
      Finset.min'_le (s := radii) (x := εC) hmem
    have hproof :
        (⟨εC, hmem⟩ : radii.Nonempty) = hradii_nonempty :=
      Subsingleton.elim _ _
    simpa [ε, hproof] using hmin_le
  have hεleRadius : ∀ i : Fin m, ε ≤ radius i := by
    intro i
    have hmem : radius i ∈ radii := by simp [radii]
    have hmin_le : radii.min' hradii_nonempty ≤ radius i :=
      Finset.min'_le (s := radii) (x := radius i) hmem
    have hproof :
        (⟨radius i, hmem⟩ : radii.Nonempty) = hradii_nonempty :=
      Subsingleton.elim _ _
    simpa [ε, hproof] using hmin_le
  refine ⟨ε, hεpos, ?_⟩
  intro t htPos htLt
  have htC : x + t • d ∈ C := hεC t htPos (lt_of_lt_of_le htLt hεleC)
  have hreprt := congrArg (fun g : (Fin n → ℝ) → EReal => g (x + t • d)) hrepr
  have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hrepr
  have hIndicatorZero_t : indicatorFunction (C := C) (x + t • d) = 0 := by
    simp [indicatorFunction, C, htC]
  have hIndicatorZero_x : indicatorFunction (C := C) x = 0 := by
    simp [indicatorFunction, C, hxC]
  have himax_mem :
      pieceAt imax (x + t • d) ∈
        {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i (x + t • d)} := by
    exact ⟨imax, himax.1, rfl⟩
  have hSetFinite :
      ({r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i (x + t • d)} : Set ℝ).Finite := by
    have hEq :
        ({r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i (x + t • d)} : Set ℝ) =
          (fun i : Fin m => pieceAt i (x + t • d)) '' (↑Iaff : Set (Fin m)) := by
      ext r
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, by simp [Iaff, hi], rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, by simpa [Iaff] using hi, rfl⟩
    rw [hEq]
    exact Set.Finite.image (fun i : Fin m => pieceAt i (x + t • d)) Iaff.finite_toSet
  have hSetBdd :
      BddAbove {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i (x + t • d)} :=
    hSetFinite.bddAbove
  have hSetNonempty :
      ({r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i (x + t • d)} : Set ℝ).Nonempty := by
    exact ⟨pieceAt imax (x + t • d), himax_mem⟩
  have hpiece_le_imax :
      ∀ i : Fin m, (i : ℕ) < k → pieceAt i (x + t • d) ≤ pieceAt imax (x + t • d) := by
    intro i hi
    by_cases hactive : pieceAt i x = (f x).toReal
    · -- Active pieces are controlled by the maximal active slope at `imax`.
      have hpiece_ray_i : pieceAt i (x + t • d) = pieceAt i x + t * slope i := by
        unfold pieceAt slope
        rw [helperForTheorem_23_10_constraint_eval_add_smul]
        ring
      have hpiece_ray_imax : pieceAt imax (x + t • d) = pieceAt imax x + t * slope imax := by
        unfold pieceAt slope
        rw [helperForTheorem_23_10_constraint_eval_add_smul]
        ring
      rw [hpiece_ray_i, hpiece_ray_imax]
      have hslope : slope i ≤ slope imax := hmax i hi hactive
      have himaxActive : pieceAt imax x = (f x).toReal := himax.2
      rw [hactive, himaxActive]
      nlinarith [le_of_lt htPos, hslope]
    · have hchosen :=
        Classical.choose_spec
          (helperForTheorem_23_10_inactiveAffine_piece_stays_below_activeSlopeMaximizer
            (f := f) (x := x) (d := d) (b := b) (β := β) (i := i) (imax := imax)
            hrepr hx hi himax hactive)
      have htRadius :
          t <
            Classical.choose
              (helperForTheorem_23_10_inactiveAffine_piece_stays_below_activeSlopeMaximizer
                (f := f) (x := x) (d := d) (b := b) (β := β)
                (i := i) (imax := imax) hrepr hx hi himax hactive) := by
        simpa [radius, hi, hactive] using (lt_of_lt_of_le htLt (hεleRadius i))
      exact le_of_lt (hchosen.2 t htPos htRadius)
  have hsup_eq :
      (sSup {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i (x + t • d)} : ℝ) =
        pieceAt imax (x + t • d) := by
    refine le_antisymm ?_ ?_
    · exact csSup_le hSetNonempty (by
        intro r hr
        rcases hr with ⟨i, hi, rfl⟩
        exact hpiece_le_imax i hi)
    · exact le_csSup hSetBdd himax_mem
  have hfx_eq :
      f x = ((pieceAt imax x : ℝ) : EReal) := by
    have hsupx :
        (sSup {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i x} : ℝ) = (f x).toReal := by
      simpa [pieceAt] using
        helperForTheorem_23_10_representationSup_eq_toReal
          (f := f) (x := x) (b := b) (β := β) hrepr hx
    calc
      f x =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i x} : ℝ) : EReal) +
            indicatorFunction (C := C) x := by
              simpa [C, pieceAt] using hreprx
      _ = ((pieceAt imax x : ℝ) : EReal) := by
        simp [hIndicatorZero_x, hsupx, himax.2, pieceAt]
  have hft_eq :
      f (x + t • d) = ((pieceAt imax (x + t • d) : ℝ) : EReal) := by
    calc
      f (x + t • d) =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = pieceAt i (x + t • d)} : ℝ) : EReal) +
            indicatorFunction (C := C) (x + t • d) := by
              simpa [C, pieceAt] using hreprt
      _ = ((pieceAt imax (x + t • d) : ℝ) : EReal) := by
        simp [hIndicatorZero_t, hsup_eq]
  have hquot_real :
      ((pieceAt imax (x + t • d) - pieceAt imax x) / t : ℝ) = slope imax := by
    have hpiece_ray_imax : pieceAt imax (x + t • d) = pieceAt imax x + t * slope imax := by
      unfold pieceAt slope
      rw [helperForTheorem_23_10_constraint_eval_add_smul]
      ring
    rw [hpiece_ray_imax]
    field_simp [ne_of_gt htPos]
    ring
  -- Rewrite both represented values in real form and divide the common numerator by `t > 0`.
  calc
    directionalDifferenceQuotientAt f x d t =
        ((((pieceAt imax (x + t • d) - pieceAt imax x) / t : ℝ) : EReal)) := by
          rw [directionalDifferenceQuotientAt, hft_eq, hfx_eq]
          simp [EReal.coe_div, EReal.coe_sub, htPos, ne_of_gt htPos]
    _ = (((slope imax : ℝ) : EReal)) := by
          exact_mod_cast hquot_real
    _ = (((∑ j, d j * b imax j : ℝ) : ℝ) : EReal) := by
          simp [slope]

/-- Helper for Theorem 23.10: a monotone quotient family on `(0, ∞)` whose values stabilize to a
constant on some punctured interval has infimum equal to that constant. -/
lemma helperForTheorem_23_10_sInf_eq_eventualConstant_on_Ioi
    (q : ℝ → EReal)
    (hmono : MonotoneOn q (Set.Ioi (0 : ℝ)))
    {c : EReal}
    (hevent : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → q t = c) :
    sInf ((Set.Ioi (0 : ℝ)).image q) = c := by
  rcases hevent with ⟨ε, hεpos, hεconst⟩
  have hhalf_pos : 0 < ε / 2 := by
    linarith
  have hhalf_lt : ε / 2 < ε := by
    linarith
  have hhalf_eq : q (ε / 2) = c := hεconst (ε / 2) hhalf_pos hhalf_lt
  have hQ_nonempty : ((Set.Ioi (0 : ℝ)).image q).Nonempty := by
    refine ⟨c, ?_⟩
    exact ⟨ε / 2, hhalf_pos, hhalf_eq⟩
  have hlower :
      ∀ z ∈ (Set.Ioi (0 : ℝ)).image q, c ≤ z := by
    intro z hz
    rcases hz with ⟨t, ht0, rfl⟩
    have ht0' : 0 < t := by
      simpa using ht0
    let s : ℝ := min (t / 2) (ε / 2)
    have hspos : 0 < s := by
      dsimp [s]
      refine lt_min ?_ hhalf_pos
      linarith
    have hsltε : s < ε := by
      dsimp [s]
      exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt
    have hsle_t : s ≤ t := by
      dsimp [s]
      refine le_trans (min_le_left _ _) ?_
      linarith
    have hqs : q s = c := hεconst s hspos hsltε
    have hmono_st : q s ≤ q t := by
      exact hmono (by simpa using hspos) (by simpa using ht0') hsle_t
    simpa [hqs] using hmono_st
  have hQ_bdd : BddBelow ((Set.Ioi (0 : ℝ)).image q) := ⟨c, hlower⟩
  have hsInf_le : sInf ((Set.Ioi (0 : ℝ)).image q) ≤ c := by
    exact csInf_le hQ_bdd ⟨ε / 2, hhalf_pos, hhalf_eq⟩
  have hc_le : c ≤ sInf ((Set.Ioi (0 : ℝ)).image q) := by
    exact le_csInf hQ_nonempty hlower
  exact le_antisymm hsInf_le hc_le

/-- Helper for Theorem 23.10: on the active-direction cone, the upper directional derivative is
the supremum of the slopes of the affine pieces active at `x`. -/
lemma helperForTheorem_23_10_upperDirectionalDerivative_eq_activeSlopeSup_of_mem_activeDirectionCone
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal} {x d : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hf : ConvexFunction f)
    (hkm : k ≤ m)
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hdTx :
      d ∈ {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
        (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}) :
    upperDirectionalDerivativeAt f x d =
      ((sSup {r : ℝ |
          ∃ i : Fin m, (i : ℕ) < k ∧
            ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
              r = ∑ j, d j * b i j} : ℝ) : EReal) := by
  let C : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  let Q : Set EReal :=
    (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x d t
  let slope : Fin m → ℝ := fun i => ∑ j, d j * b i j
  let S : Set ℝ :=
    {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧
      ((∑ j, x j * b i j) - β i) = (f x).toReal ∧ r = slope i}
  have hxC : x ∈ C := by
    -- Finiteness at `x` forces the indicator branch of the representation to vanish there.
    simpa [C] using
      helperForTheorem_23_10_finitePoint_mem_domain_of_representation
        (f := f) (x := x) (b := b) (β := β) hrepr hx
  have hmono :
      MonotoneOn (directionalDifferenceQuotientAt f x d) (Set.Ioi (0 : ℝ)) :=
    helperForTheorem_23_1_differenceQuotient_monotone f hf x d hx
  have hupper_sInf :
      upperDirectionalDerivativeAt f x d = sInf Q := by
    simpa [Q] using
      helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x d hmono
  by_cases hk0 : k = 0
  · rcases
      helperForTheorem_23_10_activeDirectionCone_smallStep_radius
        (k := k) (b := b) (β := β) (x := x) (d := d) hxC hdTx with
      ⟨ε, hεpos, hεC⟩
    have hquot_zero :
        ∃ ε : ℝ, 0 < ε ∧
          ∀ t : ℝ, 0 < t → t < ε → directionalDifferenceQuotientAt f x d t = 0 := by
      refine ⟨ε, hεpos, ?_⟩
      intro t ht0 htε
      have htC : x + t • d ∈ C := hεC t ht0 htε
      have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hrepr
      have hreprt := congrArg (fun g : (Fin n → ℝ) → EReal => g (x + t • d)) hrepr
      have hIndicatorZero_x : indicatorFunction (C := C) x = 0 := by
        simp [indicatorFunction, hxC]
      have hIndicatorZero_t : indicatorFunction (C := C) (x + t • d) = 0 := by
        simp [indicatorFunction, htC]
      have hfx_zero : f x = 0 := by
        -- In the `k = 0` branch the represented function is just the indicator of `C`.
        calc
          f x =
              ((sSup {r : ℝ |
                  ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
                indicatorFunction (C := C) x := by
                  simpa [C] using hreprx
          _ = 0 := by
                simp [hk0, hIndicatorZero_x]
      have hft_zero : f (x + t • d) = 0 := by
        -- The same small-step feasibility keeps the translated point in the indicator domain.
        calc
          f (x + t • d) =
              ((sSup {r : ℝ |
                  ∃ i : Fin m, (i : ℕ) < k ∧
                    r = (∑ j, (x + t • d) j * b i j) - β i} : ℝ) : EReal) +
                indicatorFunction (C := C) (x + t • d) := by
                  simpa [C] using hreprt
          _ = 0 := by
                simp [hk0, hIndicatorZero_t]
      rw [directionalDifferenceQuotientAt, hft_zero, hfx_zero]
      simp
    -- Route correction: the missing order step is now isolated in the eventual-constant `sInf`
    -- lemma, so the `k = 0` branch reduces to showing every small positive quotient vanishes.
    calc
      upperDirectionalDerivativeAt f x d = sInf Q := hupper_sInf
      _ = (0 : EReal) := by
        exact
          helperForTheorem_23_10_sInf_eq_eventualConstant_on_Ioi
            (q := fun t : ℝ => directionalDifferenceQuotientAt f x d t) hmono hquot_zero
      _ = ((sSup S : ℝ) : EReal) := by
        simp [S, hk0]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rcases
      helperForTheorem_23_10_exists_activeSlopeMaximizer
        (f := f) (x := x) (d := d) (b := b) (β := β) hkpos hkm hrepr hx with
      ⟨imax, himaxk, himaxActive, hmax⟩
    rcases
      helperForTheorem_23_10_directionalDifferenceQuotient_eq_activeSlopeMax_of_mem_activeDirectionCone
        (f := f) (x := x) (d := d) (b := b) (β := β)
        hrepr hx hdTx ⟨himaxk, himaxActive⟩ hmax with
      ⟨ε, hεpos, hquot⟩
    have hquot_sInf :
        sInf Q = (((slope imax : ℝ) : ℝ) : EReal) := by
      exact
        helperForTheorem_23_10_sInf_eq_eventualConstant_on_Ioi
          (q := fun t : ℝ => directionalDifferenceQuotientAt f x d t) hmono
          ⟨ε, hεpos, hquot⟩
    have hS_nonempty : S.Nonempty := by
      exact ⟨slope imax, ⟨imax, himaxk, himaxActive, rfl⟩⟩
    have hS_bdd : BddAbove S := by
      refine ⟨slope imax, ?_⟩
      intro r hr
      rcases hr with ⟨i, hi, hactive, rfl⟩
      exact hmax i hi hactive
    have hsup_eq : (sSup S : ℝ) = slope imax := by
      refine le_antisymm ?_ ?_
      · refine csSup_le hS_nonempty ?_
        intro r hr
        rcases hr with ⟨i, hi, hactive, rfl⟩
        exact hmax i hi hactive
      · exact le_csSup hS_bdd ⟨imax, himaxk, himaxActive, rfl⟩
    -- The `k > 0` branch is now an exact quotient identity plus the finite maximum property of
    -- the active slopes.
    calc
      upperDirectionalDerivativeAt f x d = sInf Q := hupper_sInf
      _ = (((slope imax : ℝ) : ℝ) : EReal) := hquot_sInf
      _ = ((sSup S : ℝ) : EReal) := by
        exact_mod_cast hsup_eq.symm

/-- Helper for Theorem 23.10: the upper directional derivative is the active-slope supremum on
the active cone and `⊤` outside it, so globally it is that supremum plus the cone indicator. -/
lemma helperForTheorem_23_10_upperDirectionalDerivative_eq_supActiveSlopes_add_indicator
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hf : ConvexFunction f)
    (hkm : k ≤ m)
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ∀ d : Fin n → ℝ,
      upperDirectionalDerivativeAt f x d =
        ((sSup {r : ℝ |
            ∃ i : Fin m, (i : ℕ) < k ∧
              ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
                r = ∑ j, d j * b i j} : ℝ) : EReal) +
          indicatorFunction
            (C := {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
              (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0})
            d := by
  intro d
  let Tx : Set (Fin n → ℝ) :=
    {d | ∀ i : Fin m, k ≤ (i : ℕ) →
      (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}
  by_cases hdTx : d ∈ Tx
  · -- On the active cone the indicator vanishes, so the inside-`Tx` slope formula is exact.
    calc
      upperDirectionalDerivativeAt f x d =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧
                ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
                  r = ∑ j, d j * b i j} : ℝ) : EReal) := by
            simpa [Tx] using
              helperForTheorem_23_10_upperDirectionalDerivative_eq_activeSlopeSup_of_mem_activeDirectionCone
                (f := f) (x := x) (d := d) (b := b) (β := β) hf hkm hrepr hx hdTx
      _ =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧
                ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
                  r = ∑ j, d j * b i j} : ℝ) : EReal) +
            indicatorFunction (C := Tx) d := by
              simp [indicatorFunction, hdTx]
  · -- Outside the active cone the represented domain exits immediately, so the indicator forces
    -- the global formula to be `⊤`.
    calc
      upperDirectionalDerivativeAt f x d = (⊤ : EReal) := by
        simpa [Tx] using
          helperForTheorem_23_10_upperDirectionalDerivative_eq_top_of_not_mem_activeDirectionCone
            (k := k) (b := b) (β := β) (f := f) hf hx hrepr hdTx
      _ =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧
                ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
                  r = ∑ j, d j * b i j} : ℝ) : EReal) +
            indicatorFunction (C := Tx) d := by
              simp [indicatorFunction, hdTx]

/-- Helper for Theorem 23.10: the active affine slopes at `x` can be reindexed by the finite
subtype of active pieces, isolating the max-affine block from the domain block. -/
lemma helperForTheorem_23_10_activeSlopeSup_reindexed {n k m : ℕ}
    (f : (Fin n → ℝ) → EReal) (x d : Fin n → ℝ)
    (b : Fin m → Fin n → ℝ) (β : Fin m → ℝ) :
    let Iact : Type := {i : Fin m //
      (i : ℕ) < k ∧ ((∑ j, x j * b i j) - β i) = (f x).toReal}
    let p : ℕ := Fintype.card Iact
    let eAct : Iact ≃ Fin p := Fintype.equivFin Iact
    ((sSup {r : ℝ |
        ∃ i : Fin m, (i : ℕ) < k ∧
          ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
            r = ∑ j, d j * b i j} : ℝ) : EReal) =
      ((sSup {r : ℝ |
          ∃ a : Fin p, r = (∑ j, d j * b (eAct.symm a).1 j) - 0} : ℝ) : EReal) := by
  let Iact : Type := {i : Fin m //
    (i : ℕ) < k ∧ ((∑ j, x j * b i j) - β i) = (f x).toReal}
  let p : ℕ := Fintype.card Iact
  let eAct : Iact ≃ Fin p := Fintype.equivFin Iact
  have hset :
      ({r : ℝ |
          ∃ i : Fin m, (i : ℕ) < k ∧
            ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
              r = ∑ j, d j * b i j} : Set ℝ) =
        {r : ℝ |
          ∃ a : Fin p, r = (∑ j, d j * b (eAct.symm a).1 j) - 0} := by
    -- Reindex the active pieces through the finite equivalence `eAct`.
    ext r
    constructor
    · rintro ⟨i, hik, hix, rfl⟩
      refine ⟨eAct ⟨i, hik, hix⟩, ?_⟩
      simp [eAct]
    · rintro ⟨a, ha⟩
      refine ⟨(eAct.symm a).1, (eAct.symm a).2.1, (eAct.symm a).2.2, ?_⟩
      simpa [sub_eq_add_neg] using ha
  -- The `sSup` values agree because the underlying real sets agree extensionally.
  exact congrArg (fun s : Set ℝ => (((sSup s : ℝ)) : EReal)) hset

/-- Helper for Theorem 23.10: the active-direction cone is exactly the intersection of the
guard-free half-spaces obtained by zeroing out inactive constraints. -/
lemma helperForTheorem_23_10_activeDirectionCone_halfspace_representation {n k m : ℕ}
    (x : Fin n → ℝ) (b : Fin m → Fin n → ℝ) (β : Fin m → ℝ) :
    let Tx : Set (Fin n → ℝ) :=
      {d | ∀ i : Fin m, k ≤ (i : ℕ) →
        (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}
    let bTx : Fin m → Fin n → ℝ := fun i =>
      if k ≤ (i : ℕ) ∧ (∑ j, x j * b i j) = β i then b i else 0
    Tx = {d : Fin n → ℝ | ∀ i : Fin m, (∑ j, d j * bTx i j) ≤ 0} := by
  let Tx : Set (Fin n → ℝ) :=
    {d | ∀ i : Fin m, k ≤ (i : ℕ) →
      (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}
  let bTx : Fin m → Fin n → ℝ := fun i =>
    if k ≤ (i : ℕ) ∧ (∑ j, x j * b i j) = β i then b i else 0
  ext d
  constructor
  · intro hdTx
    -- Active constraints keep their original normal, while inactive ones contribute `0 ≤ 0`.
    intro i
    by_cases hi : k ≤ (i : ℕ) ∧ (∑ j, x j * b i j) = β i
    · simpa [bTx, hi] using hdTx i hi.1 hi.2
    · simp [bTx, hi]
  · intro hd i hki hEq
    -- Evaluating the guard-free family on an active index recovers the original half-space.
    have hi : k ≤ (i : ℕ) ∧ (∑ j, x j * b i j) = β i := ⟨hki, hEq⟩
    simpa [bTx, hi] using hd i

/-- Helper for Theorem 23.10: after separating the active slopes from the cone normals, the
concatenated sum-index family already reproduces the active-slope supremum plus the active-cone
indicator. -/
lemma helperForTheorem_23_10_concatRepresentation_on_finSum {n p m : ℕ}
    (d : Fin n → ℝ) (bAct : Fin p → Fin n → ℝ)
    (Tx : Set (Fin n → ℝ)) (bTx : Fin m → Fin n → ℝ)
    (hTxEq : Tx = {y : Fin n → ℝ | ∀ i : Fin m, (∑ j, y j * bTx i j) ≤ 0}) :
    ((sSup {r : ℝ |
        ∃ s : Fin p ⊕ Fin m,
          ((finSumFinEquiv s : Fin (p + m))).1 < p ∧
            r = (∑ j, d j * (Sum.elim bAct bTx s) j) - 0} : ℝ) : EReal) +
      indicatorFunction
        (C := {d | ∀ s : Fin p ⊕ Fin m, p ≤ ((finSumFinEquiv s : Fin (p + m))).1 →
          (∑ j, d j * (Sum.elim bAct bTx s) j) ≤ 0})
        d =
      ((sSup {r : ℝ |
          ∃ a : Fin p, r = (∑ j, d j * bAct a j) - 0} : ℝ) : EReal) +
        indicatorFunction (C := Tx) d := by
  let bSum : Fin p ⊕ Fin m → Fin n → ℝ := Sum.elim bAct bTx
  let Ssum : Set ℝ := {r : ℝ |
    ∃ s : Fin p ⊕ Fin m,
      ((finSumFinEquiv s : Fin (p + m))).1 < p ∧
        r = (∑ j, d j * bSum s j) - 0}
  let Sact : Set ℝ := {r : ℝ |
    ∃ a : Fin p, r = (∑ j, d j * bAct a j) - 0}
  let ConeSum : Set (Fin n → ℝ) := {y : Fin n → ℝ |
    ∀ s : Fin p ⊕ Fin m, p ≤ ((finSumFinEquiv s : Fin (p + m))).1 →
      (∑ j, y j * bSum s j) ≤ 0}
  let ConeTx : Set (Fin n → ℝ) := {y : Fin n → ℝ | ∀ i : Fin m, (∑ j, y j * bTx i j) ≤ 0}
  have hsupSet :
      Ssum = Sact := by
    -- The left block of `Fin p ⊕ Fin m` is exactly the active affine family; the right block is
    -- excluded by the guard `((finSumFinEquiv s).1 < p)`.
    ext r
    constructor
    · rintro ⟨s, hs, hrs⟩
      cases s with
      | inl a =>
          exact ⟨a, by simpa [bSum] using hrs⟩
      | inr i =>
          have hge : p ≤ ((finSumFinEquiv (Sum.inr i) : Fin (p + m))).1 := by
            simpa [finSumFinEquiv_apply_right]
          exact False.elim ((not_le_of_gt hs) hge)
    · rintro ⟨a, ha⟩
      refine ⟨Sum.inl a, ?_, ?_⟩
      · simpa [finSumFinEquiv_apply_left]
      · simpa [bSum] using ha
  have hconeSet :
      ConeSum = ConeTx := by
    -- The right summands recover the cone half-spaces, while the left summands impose no
    -- condition because their `Fin (p + m)` indices are strictly below `p`.
    ext y
    constructor
    · intro hy i
      have hguard : p ≤ ((finSumFinEquiv (Sum.inr i) : Fin (p + m))).1 := by
        simpa [finSumFinEquiv_apply_right]
      simpa [bSum] using hy (Sum.inr i) hguard
    · intro hy s hs
      cases s with
      | inl a =>
          exfalso
          have : ¬ p ≤ ((finSumFinEquiv (Sum.inl a) : Fin (p + m))).1 := by
            simpa [finSumFinEquiv_apply_left]
          exact this hs
      | inr i =>
          simpa [bSum] using hy i
  have hsupEReal : (((sSup Ssum : ℝ)) : EReal) = (((sSup Sact : ℝ)) : EReal) :=
    congrArg (fun s : Set ℝ => (((sSup s : ℝ)) : EReal)) hsupSet
  have hConeIndicator :
      indicatorFunction (C := ConeSum) d = indicatorFunction (C := ConeTx) d := by
    simpa [hconeSet]
  have hTxIndicator :
      indicatorFunction (C := ConeTx) d = indicatorFunction (C := Tx) d := by
    simpa [ConeTx] using
      congrArg (fun s : Set (Fin n → ℝ) => indicatorFunction (C := s) d) hTxEq.symm
  -- Rewrite the supremum set and the cone indicator separately, then recombine them.
  have hcalc :
      (((sSup Ssum : ℝ)) : EReal) + indicatorFunction (C := ConeSum) d =
        (((sSup Sact : ℝ)) : EReal) + indicatorFunction (C := Tx) d := by
    calc
      (((sSup Ssum : ℝ)) : EReal) + indicatorFunction (C := ConeSum) d =
          (((sSup Sact : ℝ)) : EReal) + indicatorFunction (C := ConeSum) d := by
            rw [hsupEReal]
      _ = (((sSup Sact : ℝ)) : EReal) + indicatorFunction (C := ConeTx) d := by
            rw [hConeIndicator]
      _ = (((sSup Sact : ℝ)) : EReal) + indicatorFunction (C := Tx) d := by
            rw [hTxIndicator]
  simpa [bSum, Ssum, Sact, ConeSum, ConeTx] using hcalc

/-- Helper for Theorem 23.10: transporting the concatenated sum-index representation along
`finSumFinEquiv` yields the exact Chapter 19 `Fin (p + m)` witness. -/
lemma helperForTheorem_23_10_concatRepresentation_transport_to_fin {n p m : ℕ}
    (d : Fin n → ℝ) (bSum : Fin p ⊕ Fin m → Fin n → ℝ) :
    ((sSup {r : ℝ |
        ∃ i : Fin (p + m), (i : ℕ) < p ∧
          r = (∑ j, d j * bSum (finSumFinEquiv.symm i) j) - 0} : ℝ) : EReal) +
      indicatorFunction
        (C := {d | ∀ i : Fin (p + m), p ≤ (i : ℕ) →
          (∑ j, d j * bSum (finSumFinEquiv.symm i) j) ≤ 0})
        d =
      ((sSup {r : ℝ |
          ∃ s : Fin p ⊕ Fin m,
            ((finSumFinEquiv s : Fin (p + m))).1 < p ∧
              r = (∑ j, d j * bSum s j) - 0} : ℝ) : EReal) +
        indicatorFunction
          (C := {d | ∀ s : Fin p ⊕ Fin m, p ≤ ((finSumFinEquiv s : Fin (p + m))).1 →
            (∑ j, d j * bSum s j) ≤ 0})
          d := by
  let Sfin : Set ℝ := {r : ℝ |
    ∃ i : Fin (p + m), (i : ℕ) < p ∧ r = (∑ j, d j * bSum (finSumFinEquiv.symm i) j) - 0}
  let Ssum : Set ℝ := {r : ℝ |
    ∃ s : Fin p ⊕ Fin m,
      ((finSumFinEquiv s : Fin (p + m))).1 < p ∧ r = (∑ j, d j * bSum s j) - 0}
  let ConeFin : Set (Fin n → ℝ) := {y : Fin n → ℝ |
    ∀ i : Fin (p + m), p ≤ (i : ℕ) → (∑ j, y j * bSum (finSumFinEquiv.symm i) j) ≤ 0}
  let ConeSum : Set (Fin n → ℝ) := {y : Fin n → ℝ |
    ∀ s : Fin p ⊕ Fin m, p ≤ ((finSumFinEquiv s : Fin (p + m))).1 →
      (∑ j, y j * bSum s j) ≤ 0}
  have hsupSet :
      Sfin = Ssum := by
    -- Reindex the affine block by the equivalence `finSumFinEquiv`.
    ext r
    constructor
    · rintro ⟨i, hi, hri⟩
      refine ⟨finSumFinEquiv.symm i, ?_, ?_⟩
      · simpa using hi
      · simpa using hri
    · rintro ⟨s, hs, hrs⟩
      refine ⟨finSumFinEquiv s, ?_, ?_⟩
      · simpa using hs
      · simpa using hrs
  have hconeSet :
      ConeFin = ConeSum := by
    -- The indicator-domain family is the same set after reindexing by `finSumFinEquiv`.
    ext y
    constructor
    · intro hy s hs
      have := hy (finSumFinEquiv s) (by simpa using hs)
      simpa using this
    · intro hy i hi
      have := hy (finSumFinEquiv.symm i) (by simpa using hi)
      simpa using this
  have hsupEReal : (((sSup Sfin : ℝ)) : EReal) = (((sSup Ssum : ℝ)) : EReal) :=
    congrArg (fun s : Set ℝ => (((sSup s : ℝ)) : EReal)) hsupSet
  have hConeIndicator :
      indicatorFunction (C := ConeFin) d = indicatorFunction (C := ConeSum) d := by
    simpa [hconeSet]
  -- Rewrite the two ingredients of the Chapter 19 formula through the equivalence.
  have hcalc :
      (((sSup Sfin : ℝ)) : EReal) + indicatorFunction (C := ConeFin) d =
        (((sSup Ssum : ℝ)) : EReal) + indicatorFunction (C := ConeSum) d := by
    calc
      (((sSup Sfin : ℝ)) : EReal) + indicatorFunction (C := ConeFin) d =
          (((sSup Ssum : ℝ)) : EReal) + indicatorFunction (C := ConeFin) d := by
            rw [hsupEReal]
      _ = (((sSup Ssum : ℝ)) : EReal) + indicatorFunction (C := ConeSum) d := by
            rw [hConeIndicator]
  simpa [Sfin, Ssum, ConeFin, ConeSum] using hcalc

/-- Helper for Theorem 23.10: once the active slopes are reindexed and the active cone is exposed
as explicit half-spaces, the derivative should admit one Chapter 19 max-affine-plus-indicator
representation. -/
lemma helperForTheorem_23_10_upperDirectionalDerivative_representation {n k m : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (b : Fin m → Fin n → ℝ) (β : Fin m → ℝ)
    (hf : ConvexFunction f) (hkm : k ≤ m)
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ∃ (kD mD : ℕ) (bD : Fin mD → Fin n → ℝ) (βD : Fin mD → ℝ),
      kD ≤ mD ∧
        upperDirectionalDerivativeAt f x =
          fun d =>
            ((sSup {r : ℝ |
                ∃ i : Fin mD, (i : ℕ) < kD ∧
                  r = (∑ j, d j * bD i j) - βD i} : ℝ) : EReal) +
                indicatorFunction
                  (C := {d | ∀ i : Fin mD, kD ≤ (i : ℕ) →
                    (∑ j, d j * bD i j) ≤ βD i})
                d := by
  -- Route correction: the analytic part is already settled in
  -- `helperForTheorem_23_10_upperDirectionalDerivative_eq_supActiveSlopes_add_indicator`; the
  -- remaining work is purely finite bookkeeping.
  let Iact : Type := {i : Fin m //
    (i : ℕ) < k ∧ ((∑ j, x j * b i j) - β i) = (f x).toReal}
  let p : ℕ := Fintype.card Iact
  let eAct : Iact ≃ Fin p := Fintype.equivFin Iact
  let Tx : Set (Fin n → ℝ) :=
    {d | ∀ i : Fin m, k ≤ (i : ℕ) →
      (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}
  let bTx : Fin m → Fin n → ℝ := fun i =>
    if k ≤ (i : ℕ) ∧ (∑ j, x j * b i j) = β i then b i else 0
  let bSum : Fin p ⊕ Fin m → Fin n → ℝ := Sum.elim (fun a => b (eAct.symm a).1) bTx
  let bD : Fin (p + m) → Fin n → ℝ := fun i => bSum (finSumFinEquiv.symm i)
  let βD : Fin (p + m) → ℝ := fun _ => 0
  refine ⟨p, p + m, bD, βD, Nat.le_add_right p m, ?_⟩
  ext d
  have hderivFormula :=
    helperForTheorem_23_10_upperDirectionalDerivative_eq_supActiveSlopes_add_indicator
      (f := f) (x := x) (b := b) (β := β) hf hkm hrepr hx
  have hTxEq :
      Tx = {y : Fin n → ℝ | ∀ i : Fin m, (∑ j, y j * bTx i j) ≤ 0} := by
    -- Reuse the explicit half-space representation of the active-direction cone.
    simpa [Tx, bTx] using
      helperForTheorem_23_10_activeDirectionCone_halfspace_representation
        (k := k) (x := x) (b := b) (β := β)
  have hactiveReindex :=
    helperForTheorem_23_10_activeSlopeSup_reindexed
      (k := k) (f := f) (x := x) (d := d) (b := b) (β := β)
  have hconcat :=
    helperForTheorem_23_10_concatRepresentation_on_finSum
      (d := d) (bAct := fun a => b (eAct.symm a).1) (Tx := Tx) (bTx := bTx) hTxEq
  have htransport :=
    helperForTheorem_23_10_concatRepresentation_transport_to_fin
      (d := d) (bSum := bSum)
  -- First rewrite the derivative by the proved active-slope formula, then package the active
  -- block and cone block into one `Fin (p + m)` family.
  calc
    upperDirectionalDerivativeAt f x d =
        ((sSup {r : ℝ |
            ∃ i : Fin m, (i : ℕ) < k ∧
              ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
                r = ∑ j, d j * b i j} : ℝ) : EReal) +
          indicatorFunction (C := Tx) d := by
            simpa [Tx] using hderivFormula d
    _ =
        ((sSup {r : ℝ |
            ∃ a : Fin p, r = (∑ j, d j * b (eAct.symm a).1 j) - 0} : ℝ) : EReal) +
          indicatorFunction (C := Tx) d := by
            rw [hactiveReindex]
    _ =
        ((sSup {r : ℝ |
            ∃ s : Fin p ⊕ Fin m,
              ((finSumFinEquiv s : Fin (p + m))).1 < p ∧
                r = (∑ j, d j * bSum s j) - 0} : ℝ) : EReal) +
          indicatorFunction
            (C := {d | ∀ s : Fin p ⊕ Fin m, p ≤ ((finSumFinEquiv s : Fin (p + m))).1 →
              (∑ j, d j * bSum s j) ≤ 0})
            d := by
              exact hconcat.symm
    _ =
        ((sSup {r : ℝ |
            ∃ i : Fin (p + m), (i : ℕ) < p ∧
              r = (∑ j, d j * bD i j) - 0} : ℝ) : EReal) +
          indicatorFunction
            (C := {d | ∀ i : Fin (p + m), p ≤ (i : ℕ) →
              (∑ j, d j * bD i j) ≤ 0})
            d := by
              exact htransport.symm
    _ =
        ((sSup {r : ℝ |
            ∃ i : Fin (p + m), (i : ℕ) < p ∧
              r = (∑ j, d j * bD i j) - βD i} : ℝ) : EReal) +
          indicatorFunction
            (C := {d | ∀ i : Fin (p + m), p ≤ (i : ℕ) →
              (∑ j, d j * bD i j) ≤ βD i})
            d := by
              simp [βD]

/-- Theorem 23.10: If `f` is a polyhedral convex function and `f x` is finite, then `f` is
subdifferentiable at `x`, the subdifferential `∂ f(x)` is a polyhedral convex set, and the
directional-derivative function `y ↦ f'(x; y)` is a proper polyhedral convex function equal to the
support function of `∂ f(x)`. -/
theorem polyhedralConvex_subdifferentiable_and_subdifferential_polyhedral {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hpoly : IsPolyhedralConvexFunction n f)
    {x : Fin n → ℝ} (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    Set.Nonempty (subdifferentialAt f x) ∧
      IsPolyhedralConvexFunction n (indicatorFunction ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) ∧
      ProperConvexFunctionOn Set.univ (upperDirectionalDerivativeAt f x) ∧
      IsPolyhedralConvexFunction n (upperDirectionalDerivativeAt f x) ∧
      upperDirectionalDerivativeAt f x = subdifferentialSupportAt f x := by
  -- First upgrade the finite-point hypothesis to the global non-`⊥` side condition required by
  -- the Chapter 19 max-affine-plus-indicator representation theorem.
  have hnonbot :
      ∀ z : Fin n → ℝ, f z ≠ (⊥ : EReal) :=
    helperForTheorem_23_10_pointwise_ne_bot_of_polyhedral_finitePoint f hpoly hx
  have hrepr :
      ∃ (k m : ℕ) (b : Fin m → Fin n → ℝ) (β : Fin m → ℝ),
        k ≤ m ∧
          f =
            fun y =>
              ((sSup {r : ℝ |
                  ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
                indicatorFunction
                  (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                    (∑ j, y j * b i j) ≤ β i})
                  y := by
    exact
      (polyhedral_convex_function_iff_max_affine_plus_indicator
        (n := n) (f := f)).1 ⟨hpoly, hnonbot⟩
  rcases hrepr with ⟨k, m, b, β, hkm, hrepr⟩
  let C : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  let Tx : Set (Fin n → ℝ) :=
    {d | ∀ i : Fin m, k ≤ (i : ℕ) →
      (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}
  -- Route correction: the translated-domain route was too strong; the derivative only sees the
  -- active-constraint cone determined by sufficiently small positive steps from `x`.
  have hxC : x ∈ C := by
    -- The representation can stay finite at `x` only if the indicator term vanishes there.
    simpa [C] using
      helperForTheorem_23_10_finitePoint_mem_domain_of_representation
        (f := f) (x := x) (b := b) (β := β) hrepr hx
  have hTxData : IsPolyhedralConvexSet n Tx ∧ (0 : Fin n → ℝ) ∈ Tx := by
    -- Package the active-direction cone as a finite intersection of homogeneous half-spaces.
    simpa [Tx] using
      helperForTheorem_23_10_activeDirectionCone_polyhedral_of_representation
        (k := k) (b := b) (β := β) (x := x)
  have hTxExit :
      ∀ d : Fin n → ℝ, d ∉ Tx →
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → x + t • d ∉ C := by
    intro d hdTx
    -- Directions outside the active cone violate one active constraint immediately.
    simpa [C, Tx] using
      helperForTheorem_23_10_not_mem_activeDirectionCone_eventually_not_domain
        (b := b) (β := β) (x := x) (d := d) hdTx
  have hTxNecessary :
      ∀ d : Fin n → ℝ,
        (∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → x + t • d ∈ C) → d ∈ Tx := by
    intro d hd
    -- Any active constraint with positive slope would be violated at the half-step `ε / 2`.
    simpa [C, Tx] using
      helperForTheorem_23_10_activeDirectionCone_eventually_domain_only_if
        (b := b) (β := β) (x := x) (d := d) hd
  have hTxSufficient :
      ∀ d : Fin n → ℝ,
        d ∈ Tx → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → x + t • d ∈ C := by
    intro d hd
    -- Route correction: finish the local-domain packaging first, so later derivative arguments can
    -- cleanly split into the `d ∈ Tx` and `d ∉ Tx` cases.
    simpa [C, Tx] using
      helperForTheorem_23_10_activeDirectionCone_smallStep_radius
        (k := k) (b := b) (β := β) (x := x) (d := d) hxC hd
  have hTxEventually_iff :
      ∀ d : Fin n → ℝ,
        (∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → x + t • d ∈ C) ↔ d ∈ Tx := by
    intro d
    constructor
    · exact hTxNecessary d
    · exact hTxSufficient d
  have hf : ConvexFunction f := by
    -- The represented function is already known to be convex from the polyhedral hypothesis.
    simpa [ConvexFunction] using hpoly.1
  have hupperOutside :
      ∀ d : Fin n → ℝ, d ∉ Tx → upperDirectionalDerivativeAt f x d = (⊤ : EReal) := by
    intro d hdTx
    -- Outside the active cone, the indicator term becomes `⊤` on a whole punctured neighborhood.
    simpa [Tx] using
      helperForTheorem_23_10_upperDirectionalDerivative_eq_top_of_not_mem_activeDirectionCone
        (k := k) (b := b) (β := β) (f := f) hf hx hrepr hdTx
  have hderivFormula :
      ∀ d : Fin n → ℝ,
        upperDirectionalDerivativeAt f x d =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧
                ((∑ j, x j * b i j) - β i) = (f x).toReal ∧
                  r = ∑ j, d j * b i j} : ℝ) : EReal) +
            indicatorFunction (C := Tx) d :=
    helperForTheorem_23_10_upperDirectionalDerivative_eq_supActiveSlopes_add_indicator
      (f := f) (x := x) (b := b) (β := β) hf hkm hrepr hx
  have hreprD :
      ∃ (kD mD : ℕ) (bD : Fin mD → Fin n → ℝ) (βD : Fin mD → ℝ),
        kD ≤ mD ∧
          upperDirectionalDerivativeAt f x =
            fun d =>
              ((sSup {r : ℝ |
                  ∃ i : Fin mD, (i : ℕ) < kD ∧
                    r = (∑ j, d j * bD i j) - βD i} : ℝ) : EReal) +
                indicatorFunction
                  (C := {d | ∀ i : Fin mD, kD ≤ (i : ℕ) →
                    (∑ j, d j * bD i j) ≤ βD i})
                  d :=
    helperForTheorem_23_10_upperDirectionalDerivative_representation
      (f := f) (x := x) (b := b) (β := β) hf hkm hrepr hx
  have hpolyD : IsPolyhedralConvexFunction n (upperDirectionalDerivativeAt f x) :=
    ((polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := upperDirectionalDerivativeAt f x)).2 hreprD).1
  have hnonbotD :
      ∀ d : Fin n → ℝ, upperDirectionalDerivativeAt f x d ≠ (⊥ : EReal) :=
    helperForText_19_0_9_representable_pointwise_ne_bot (f := upperDirectionalDerivativeAt f x)
      hreprD
  have hzeroD : upperDirectionalDerivativeAt f x 0 = 0 :=
    helperForTheorem_23_1_upperDerivative_zero f x hx
  have hDproper : ProperConvexFunctionOn Set.univ (upperDirectionalDerivativeAt f x) := by
    refine ⟨hpolyD.1, ?_, ?_⟩
    · -- The zero direction is finite, so the derivative has a finite epigraph point.
      refine ⟨(0, 0), ?_⟩
      refine (mem_epigraph_univ_iff (f := upperDirectionalDerivativeAt f x)).2 ?_
      simpa [hzeroD]
    · -- The Chapter 19 representation already rules out `⊥` everywhere.
      intro d _
      exact hnonbotD d
  have hclosureEq :
      convexFunctionClosure (upperDirectionalDerivativeAt f x) = subdifferentialSupportAt f x := by
    -- Theorem 23.2 gives the closure/support identity for every finite convex point.
    simpa using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf x hx (0 : Module.Dual ℝ (Fin n → ℝ))).2.2.2
  have hclosureSelf :
      convexFunctionClosure (upperDirectionalDerivativeAt f x) = upperDirectionalDerivativeAt f x :=
    helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
      (g := upperDirectionalDerivativeAt f x) hpolyD hDproper
  have hDirEq : upperDirectionalDerivativeAt f x = subdifferentialSupportAt f x := by
    -- Remove the closure using polyhedral properness.
    calc
      upperDirectionalDerivativeAt f x = convexFunctionClosure (upperDirectionalDerivativeAt f x) := by
        symm
        exact hclosureSelf
      _ = subdifferentialSupportAt f x := hclosureEq
  have hsubNE : Set.Nonempty (subdifferentialAt f x) := by
    by_contra hEmpty
    -- If the subdifferential were empty, Theorem 23.3 would force the derivative to be improper.
    exact
      (helperForTheorem_23_3_directionalDerivative_improper_of_empty_subdifferential
        f hf x hx hEmpty).2 hDproper
  let S : Set (Fin n → ℝ) := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
  have hSClosed : IsClosed S := by
    simpa [S] using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf x hx (0 : Module.Dual ℝ (Fin n → ℝ))).2.1
  have hSConv : Convex ℝ S := by
    simpa [S] using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf x hx (0 : Module.Dual ℝ (Fin n → ℝ))).2.2.1
  have hSupportEq : supportFunctionEReal S = upperDirectionalDerivativeAt f x := by
    -- Rewrite the subdifferential support through the coordinate preimage description.
    ext d
    calc
      supportFunctionEReal S d = subdifferentialSupportAt f x d := by
        simpa [S] using helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x d
      _ = upperDirectionalDerivativeAt f x d := by
        simpa using (congrFun hDirEq d).symm
  have hSupportPoly : IsPolyhedralConvexFunction n (supportFunctionEReal S) := by
    simpa [hSupportEq] using hpolyD
  have hSpoly : IsPolyhedralConvexSet n S := by
    exact
      (polyhedral_convexSet_iff_supportFunction_polyhedral (n := n) (C := S)
        hSClosed hSConv).mpr hSupportPoly
  have hIndicatorPoly :
      IsPolyhedralConvexFunction n (indicatorFunction S) :=
    helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet hSpoly
  exact ⟨hsubNE, by simpa [S] using hIndicatorPoly, hDproper, hpolyD, hDirEq⟩

end Section23
end Chap05
