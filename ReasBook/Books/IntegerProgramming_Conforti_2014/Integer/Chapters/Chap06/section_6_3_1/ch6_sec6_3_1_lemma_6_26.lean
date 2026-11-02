import Mathlib

-- Semantic recall note: no deferred semantic search tool such as `lean_leansearch` was available
-- in this environment, so this file uses direct `Set.Icc` / `Set.EqOn` mathlib primitives.

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma626

open Set

/-- A real-valued function is bounded on bounded intervals if the image of every closed interval is
a bounded subset of `ℝ`. The source-facing absolute-value formulation is given by
`boundedOnBoundedIntervals_iff`. -/
def BoundedOnBoundedIntervals (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, Bornology.IsBounded (f '' Icc x y)

/-- A function that is bounded on bounded intervals maps every bounded subset of `ℝ` to a bounded
subset. This is the bridge to the canonical `LocallyBoundedMap` API. -/
theorem BoundedOnBoundedIntervals.isBounded_image {f : ℝ → ℝ} (hf : BoundedOnBoundedIntervals f)
    {s : Set ℝ} (hs : Bornology.IsBounded s) : Bornology.IsBounded (f '' s) := by
  refine Bornology.IsBounded.subset (hf (sInf s) (sSup s)) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hs.subset_Icc_sInf_sSup hx, rfl⟩

/-- A function bounded on bounded intervals yields a canonical locally bounded map. -/
def BoundedOnBoundedIntervals.toLocallyBoundedMap {f : ℝ → ℝ}
    (hf : BoundedOnBoundedIntervals f) : LocallyBoundedMap ℝ ℝ :=
  LocallyBoundedMap.ofMapBounded f fun _ hs ↦ hf.isBounded_image hs

/-- `BoundedOnBoundedIntervals f` unfolds to a uniform absolute-value bound on each bounded
closed interval. -/
theorem boundedOnBoundedIntervals_iff {f : ℝ → ℝ} :
    BoundedOnBoundedIntervals f ↔
      ∀ x y : ℝ, x ≤ y → ∃ M : ℝ, ∀ z ∈ Icc x y, |f z| ≤ M := by
  constructor
  · intro hf x y hxy
    -- Convert boundedness of the image set into a uniform absolute-value bound.
    obtain ⟨M, hM⟩ := Bornology.IsBounded.exists_norm_le (hf x y)
    refine ⟨M, fun z hz ↦ ?_⟩
    simpa [Real.norm_eq_abs] using hM _ ⟨z, hz, rfl⟩
  · intro hf x y
    by_cases hxy : x ≤ y
    · rcases hf x y hxy with ⟨M, hM⟩
      -- A pointwise absolute-value bound puts the whole image inside a bounded order interval.
      refine (Metric.isBounded_of_abs_le M).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      exact hM z hz
    · have hIcc : Icc x y = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hxy)
      simp [hIcc]

/-- Helper for Lemma 6.26: local additivity on an initial interval forces the value at `0` to
vanish. -/
lemma local_additive_zero
    {φ : ℝ → ℝ} {m : ℝ}
    (hm : 0 ≤ m)
    (hadd : ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 m → y ∈ Icc 0 m → x + y ∈ Icc 0 m →
      φ (x + y) = φ x + φ y) :
    φ 0 = 0 := by
  have h0 : (0 : ℝ) ∈ Icc 0 m := by simp [hm]
  -- Evaluate the additive law at `(0, 0)` and cancel one copy of `φ 0`.
  have h := hadd h0 h0 (by simpa using h0)
  have h' := congrArg (fun t ↦ t - φ 0) h
  simpa using h'.symm

/-- Helper for Lemma 6.26: repeated equal increments compute a natural multiple as long as each
partial sum stays in range. -/
lemma local_additive_nat_mul
    {φ : ℝ → ℝ} {L m u : ℝ}
    (hadd : ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 L → y ∈ Icc 0 m → x + y ∈ Icc 0 L →
      φ (x + y) = φ x + φ y)
    (hu : u ∈ Icc 0 m)
    {n : Nat}
    (hnu : (n : ℝ) * u ∈ Icc 0 L) :
    φ ((n : ℝ) * u) = (n : ℝ) * φ u := by
  induction n with
  | zero =>
      -- The zero multiple is the previously isolated base case.
      have hm_nonneg : 0 ≤ m := le_trans hu.1 hu.2
      have h0L : (0 : ℝ) ∈ Icc 0 L := by simpa using hnu
      have h0m : (0 : ℝ) ∈ Icc 0 m := by simp [hm_nonneg]
      have hzero := hadd h0L h0m (by simpa using h0L)
      have hzero' := congrArg (fun t ↦ t - φ 0) hzero
      simpa using hzero'.symm
  | succ n ihn =>
      have hx : (n : ℝ) * u ∈ Icc 0 L := by
        constructor
        · nlinarith [hu.1]
        · have hu_nonneg : 0 ≤ u := hu.1
          have hsum_le : (n : ℝ) * u + u ≤ L := by
            simpa [Nat.cast_add, add_mul, one_mul, add_comm, add_left_comm, add_assoc] using hnu.2
          nlinarith
      have hsum : (n : ℝ) * u + u ∈ Icc 0 L := by
        simpa [Nat.cast_add, add_mul, one_mul, add_comm, add_left_comm, add_assoc] using hnu
      have hsucc_mul : (((n + 1 : Nat) : ℝ) * u) = (n : ℝ) * u + u := by
        norm_num [Nat.cast_add]
        ring
      have hsucc_mul_phi : (n : ℝ) * φ u + φ u = ((n + 1 : Nat) : ℝ) * φ u := by
        norm_num [Nat.cast_add]
        ring
      -- One more application of the local additive law advances the progression by one step.
      calc
        φ (((n + 1 : Nat) : ℝ) * u)
            = φ ((n : ℝ) * u + u) := by rw [hsucc_mul]
        _ = φ ((n : ℝ) * u) + φ u := hadd hx hu hsum
        _ = (n : ℝ) * φ u + φ u := by rw [ihn hx]
        _ = ((n + 1 : Nat) : ℝ) * φ u := hsucc_mul_phi

/-- Helper for Lemma 6.26: if the endpoint value is zero, then every rational multiple of the
endpoint also has value zero. -/
lemma local_additive_rat_mul_zero
    {φ : ℝ → ℝ} {m : ℝ}
    (hm : 0 < m)
    (hadd : ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 m → y ∈ Icc 0 m → x + y ∈ Icc 0 m →
      φ (x + y) = φ x + φ y)
    (hm0 : φ m = 0)
    {q : ℚ}
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    φ ((q : ℝ) * m) = 0 := by
  let qnn : ℚ≥0 := ⟨q, hq0⟩
  have hden : (0 : ℝ) < qnn.den := by
    exact_mod_cast NNRat.den_pos qnn
  have hqeq : (q : ℝ) = qnn.num / qnn.den := by
    have hqeq_qnn : ((qnn : ℚ) : ℝ) = (qnn.num : ℝ) / qnn.den := by
      rw [← Rat.num_div_den (qnn : ℚ)]
      norm_num [NNRat.num_coe, NNRat.den_coe]
    simpa [qnn, NNRat.num, NNRat.den, Rat.num_nonneg.mpr hq0, abs_of_nonneg] using hqeq_qnn
  have hp_le_real : (qnn.num : ℝ) ≤ qnn.den := by
    have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
    rw [hqeq] at hq1'
    exact (div_le_one hden).1 hq1'
  have hp_le : qnn.num ≤ qnn.den := by
    exact_mod_cast hp_le_real
  let u : ℝ := m / qnn.den
  have hu : u ∈ Icc 0 m := by
    constructor
    · positivity
    · have hone_nat : 1 ≤ qnn.den := Nat.succ_le_of_lt (NNRat.den_pos qnn)
      have hone : (1 : ℝ) ≤ qnn.den := by exact_mod_cast hone_nat
      simpa [u] using div_le_self hm.le hone
  have hum_eq : (qnn.den : ℝ) * u = m := by
    dsimp [u]
    field_simp [hden.ne']
  have hum : ((qnn.den : ℝ) * u) ∈ Icc 0 m := by
    simpa [hum_eq] using (show m ∈ Icc 0 m by simp [hm.le])
  have hu_zero : φ u = 0 := by
    have hmul_zero : (qnn.den : ℝ) * φ u = 0 := by
      calc
        (qnn.den : ℝ) * φ u = φ ((qnn.den : ℝ) * u) := by
          symm
          exact local_additive_nat_mul hadd hu hum
        _ = φ m := by rw [hum_eq]
        _ = 0 := hm0
    nlinarith
  have hpum : (qnn.num : ℝ) * u ∈ Icc 0 m := by
    constructor
    · positivity
    · have hu_nonneg : 0 ≤ u := hu.1
      have : (qnn.num : ℝ) * u ≤ (qnn.den : ℝ) * u := by
        gcongr
      simpa [hum_eq] using this.trans hum.2
  -- Express the target as a natural multiple of `u = m / q.den`.
  have hqmul : (q : ℝ) * m = (qnn.num : ℝ) * u := by
    rw [hqeq]
    dsimp [u]
    field_simp [hden.ne']
  calc
    φ ((q : ℝ) * m) = φ ((qnn.num : ℝ) * u) := by rw [hqmul]
    _ = (qnn.num : ℝ) * φ u := local_additive_nat_mul hadd hu hpum
    _ = 0 := by simp [hu_zero]

/-- Helper for Lemma 6.26: bounded local additivity makes the function small near `0`. -/
lemma local_additive_small_near_zero
    {φ : ℝ → ℝ} {m : ℝ}
    (hm : 0 < m)
    (hadd : ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 m → y ∈ Icc 0 m → x + y ∈ Icc 0 m →
      φ (x + y) = φ x + φ y)
    (hbound : ∃ R > 0, ∀ x ∈ Icc 0 m, |φ x| ≤ R) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Icc 0 m, x < δ → |φ x| < ε := by
  intro ε hε
  rcases hbound with ⟨R, hRpos, hR⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (R / ε)
  have hNpos : (0 : ℝ) < N := by
    have : 0 < R / ε := by positivity
    exact lt_trans this hN
  refine ⟨m / N, div_pos hm hNpos, ?_⟩
  intro x hx hxδ
  have hNx : (N : ℝ) * x ∈ Icc 0 m := by
    constructor
    · nlinarith [hx.1]
    · have : (N : ℝ) * x < (N : ℝ) * (m / N) := by
        exact mul_lt_mul_of_pos_left hxδ hNpos
      have hmul : (N : ℝ) * (m / N) = m := by field_simp [hNpos.ne']
      linarith
  have hmul : (N : ℝ) * |φ x| ≤ R := by
    calc
      (N : ℝ) * |φ x| = |(N : ℝ) * φ x| := by
        rw [abs_mul, abs_of_nonneg hNpos.le]
      _ = |φ ((N : ℝ) * x)| := by
        rw [local_additive_nat_mul hadd hx hNx]
      _ ≤ R := hR _ hNx
  have hR_lt : R < (N : ℝ) * ε := by
    exact (div_lt_iff₀ hε).1 hN
  by_contra hxe
  have hε_le : ε ≤ |φ x| := le_of_not_gt hxe
  have hNε : (N : ℝ) * ε ≤ R := by
    calc
      (N : ℝ) * ε ≤ (N : ℝ) * |φ x| := by gcongr
      _ ≤ R := hmul
  linarith

/-- Helper for Lemma 6.26: a bounded locally additive function on `[0,m]` that vanishes at `m`
must vanish everywhere on `[0,m]`. -/
lemma local_additive_eq_zero_of_endpoint_zero
    {φ : ℝ → ℝ} {m : ℝ}
    (hm : 0 < m)
    (hadd : ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 m → y ∈ Icc 0 m → x + y ∈ Icc 0 m →
      φ (x + y) = φ x + φ y)
    (hbound : ∃ R > 0, ∀ x ∈ Icc 0 m, |φ x| ≤ R)
    (hm0 : φ m = 0) :
    (Icc 0 m).EqOn φ (fun _ ↦ 0) := by
  intro x hx
  have hzero : φ 0 = 0 := local_additive_zero hm.le hadd
  by_contra hx0
  have hε : 0 < |φ x| := abs_pos.mpr hx0
  rcases local_additive_small_near_zero hm hadd hbound |φ x| hε with ⟨δ, hδpos, hδ⟩
  have hxpos : 0 < x := by
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact hx0 (hxeq ▸ hzero)
    exact lt_of_le_of_ne hx.1 (by simpa [eq_comm] using hx_ne)
  let η : ℝ := min (δ / 2) x
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min (by linarith) hxpos
  have hη_le_x : η ≤ x := by
    dsimp [η]
    exact min_le_right _ _
  have hlow_lt_high : (x - η) / m < x / m := by
    exact (div_lt_div_iff_of_pos_right hm).2 (by linarith)
  obtain ⟨q, hq_left, hq_right⟩ := exists_rat_btwn hlow_lt_high
  have hq0 : 0 ≤ q := by
    have hq0_real : (0 : ℝ) ≤ q := by
      have : 0 ≤ (x - η) / m := by
        apply div_nonneg
        · linarith
        · exact hm.le
      exact this.trans (le_of_lt hq_left)
    exact_mod_cast hq0_real
  have hq1 : q ≤ 1 := by
    have hq1_real : (q : ℝ) ≤ 1 := by
      have hx_div : x / m ≤ 1 := (div_le_one hm).2 hx.2
      exact le_of_lt <| hq_right.trans_le hx_div
    exact_mod_cast hq1_real
  let r : ℝ := (q : ℝ) * m
  have hr_mem : r ∈ Icc 0 m := by
    constructor
    · dsimp [r]
      positivity
    · dsimp [r]
      have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
      nlinarith
  have hr_zero : φ r = 0 := local_additive_rat_mul_zero hm hadd hm0 hq0 hq1
  have hxr_nonneg : 0 ≤ x - r := by
    have hr_lt_x : r < x := by
      dsimp [r]
      exact (lt_div_iff₀ hm).1 hq_right
    linarith
  have hxr_lt : x - r < δ := by
    have hxr_gt : x - η < r := by
      dsimp [r]
      exact (div_lt_iff₀ hm).1 hq_left
    have hη_lt_δ : η < δ := by
      dsimp [η]
      exact (min_lt_iff.2 <| Or.inl <| by linarith)
    linarith
  have hxr_mem : x - r ∈ Icc 0 m := by
    constructor
    · exact hxr_nonneg
    · linarith [hx.2, hr_mem.1]
  -- Split `x` into the rational multiple `r` plus a small remainder.
  have hsplit : φ x = φ r + φ (x - r) := by
    have hsum_mem : r + (x - r) ∈ Icc 0 m := by
      simpa [r, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx
    have := hadd hr_mem hxr_mem hsum_mem
    simpa [r, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hsmall : |φ (x - r)| < |φ x| := hδ _ hxr_mem hxr_lt
  have : |φ x| < |φ x| := by
    rw [hsplit, hr_zero, zero_add] at hsmall
    simpa using hsmall
  exact (lt_irrefl _ this).elim

/-- Helper for Lemma 6.26: bounded local additivity on `[0,m]` forces an affine formula with a
single slope. -/
lemma affine_on_initial_interval_of_bounded_local_add
    {φ : ℝ → ℝ} {m : ℝ}
    (hm : 0 < m)
    (hadd : ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 m → y ∈ Icc 0 m → x + y ∈ Icc 0 m →
      φ (x + y) = φ x + φ y)
    (hbound : ∃ R > 0, ∀ x ∈ Icc 0 m, |φ x| ≤ R) :
    ∃ c : ℝ, (Icc 0 m).EqOn φ (fun x ↦ c * x) := by
  let c : ℝ := φ m / m
  let ψ : ℝ → ℝ := fun x ↦ φ x - c * x
  have hψ_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 m → y ∈ Icc 0 m → x + y ∈ Icc 0 m →
        ψ (x + y) = ψ x + ψ y := by
    intro x y hx hy hxy
    -- Subtract the same linear part from both sides of the additive law.
    dsimp [ψ]
    rw [hadd hx hy hxy]
    ring
  have hψ_bound : ∃ R > 0, ∀ x ∈ Icc 0 m, |ψ x| ≤ R := by
    rcases hbound with ⟨R, hRpos, hR⟩
    refine ⟨R + |c| * m, by positivity, ?_⟩
    intro x hx
    have hx_abs : |x| ≤ m := by simpa [abs_of_nonneg hx.1] using hx.2
    have hcx : |c * x| ≤ |c| * m := by
      rw [abs_mul]
      gcongr
    calc
      |ψ x| = |φ x - c * x| := by rfl
      _ ≤ |φ x| + |c * x| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le (φ x) (-c * x)
      _ ≤ R + |c| * m := by gcongr; exact hR _ hx
  have hcm : c * m = φ m := by
    dsimp [c]
    field_simp [hm.ne']
  have hψm : ψ m = 0 := by
    dsimp [ψ]
    rw [hcm]
    ring
  refine ⟨c, ?_⟩
  intro x hx
  -- The centered function `ψ` vanishes on the whole interval, so `φ` is exactly linear there.
  have hψx := local_additive_eq_zero_of_endpoint_zero hm hψ_add hψ_bound hψm hx
  dsimp [ψ, c] at hψx
  linarith

/-- Helper for Lemma 6.26: once the slope is known on a small initial interval, repeated equal-step
decompositions extend it to the whole larger interval. -/
lemma linear_extension_from_initial_interval
    {φ : ℝ → ℝ} {m L c : ℝ}
    (hm : 0 < m)
    (hadd : ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 L → y ∈ Icc 0 m → x + y ∈ Icc 0 L →
      φ (x + y) = φ x + φ y)
    (hsmall : (Icc 0 m).EqOn φ (fun x ↦ c * x)) :
    (Icc 0 L).EqOn φ (fun x ↦ c * x) := by
  intro x hx
  obtain ⟨N, hN⟩ := exists_nat_gt (x / m)
  have hNpos : (0 : ℝ) < N := by
    have : 0 ≤ x / m := by exact div_nonneg hx.1 hm.le
    exact this.trans_lt hN
  let u : ℝ := x / N
  have hu : u ∈ Icc 0 m := by
    constructor
    · exact div_nonneg hx.1 hNpos.le
    · have hxlt : x < (N : ℝ) * m := (div_lt_iff₀ hm).1 hN
      dsimp [u]
      exact (div_le_iff₀ hNpos).2 (by simpa [mul_comm] using le_of_lt hxlt)
  have hNx : (N : ℝ) * u ∈ Icc 0 L := by
    have : (N : ℝ) * u = x := by
      dsimp [u]
      field_simp [hNpos.ne']
    simpa [this] using hx
  -- Divide the point `x` into `N` equal pieces, use the small-interval formula on each piece,
  -- and sum back up.
  calc
    φ x = φ ((N : ℝ) * u) := by
      congr
      dsimp [u]
      field_simp [hNpos.ne']
    _ = (N : ℝ) * φ u := local_additive_nat_mul hadd hu hNx
    _ = (N : ℝ) * (c * u) := by rw [hsmall hu]
    _ = c * x := by
      dsimp [u]
      field_simp [hNpos.ne']

/-- Helper for Lemma 6.26: every point of `[0, la + lb]` splits as a sum of one point in
`[0, la]` and one point in `[0, lb]`. -/
lemma sum_interval_decomposition_zero
    {la lb z : ℝ}
    (hla : 0 ≤ la)
    (hlb : 0 ≤ lb)
    (hz : z ∈ Icc 0 (la + lb)) :
    ∃ x ∈ Icc 0 la, ∃ y ∈ Icc 0 lb, z = x + y := by
  let x : ℝ := min z la
  let y : ℝ := z - x
  refine ⟨x, ?_, y, ?_, by dsimp [y]; linarith⟩
  · constructor
    · dsimp [x]
      exact le_min hz.1 hla
    · dsimp [x]
      exact min_le_right _ _
  · constructor
    · dsimp [x, y]
      linarith [min_le_left z la]
    · dsimp [x, y]
      have hlower : z - lb ≤ min z la := by
        refine le_min ?_ ?_
        · linarith
        · linarith [hz.2]
      linarith

/-- Existence of an affine comparison map with linear part `x ↦ c * x` is equivalent to the
source-facing intercept form `x ↦ c * x + d`. -/
theorem exists_affineMap_eqOn_iff {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ} :
    (∃ g : ℝ →ᵃ[ℝ] ℝ, g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c ∧ s.EqOn f g) ↔
      ∃ d : ℝ, s.EqOn f (fun x ↦ c * x + d) := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    refine ⟨g 0, ?_⟩
    intro x hx
    calc
      f x = g x := hfg hx
      _ = g.linear x + g 0 := by simpa [vadd_eq_add] using g.map_vadd 0 x
      _ = c * x + g 0 := by simp [hg, LinearMap.smulRight_apply, mul_comm]
  · rintro ⟨d, hfd⟩
    refine ⟨((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c).toAffineMap +ᵥ AffineMap.const ℝ ℝ d,
      by simp, ?_⟩
    intro x hx
    simpa [vadd_eq_add, mul_comm] using hfd hx

/-- Lemma 6.26 (Interval Lemma). Let `A := [a₁, a₂]`, `B := [b₁, b₂]`, and
`A + B := [a₁ + b₁, a₂ + b₂]`. If `f : ℝ → ℝ` is bounded on every bounded interval and satisfies
`f a + f b = f (a + b)` for all `a ∈ A` and `b ∈ B`, then `f` is affine on `A`, on `B`, and on
`A + B`, with the same slope on all three intervals. -/
theorem interval_lemma_affine_with_common_slope
    {f : ℝ → ℝ}
    (h_bdd : BoundedOnBoundedIntervals f)
    {a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ < a₂)
    (hb : b₁ < b₂)
    (h_add :
      ∀ ⦃a b : ℝ⦄, a ∈ Icc a₁ a₂ → b ∈ Icc b₁ b₂ → f a + f b = f (a + b)) :
    ∃ c : ℝ, ∃ gA gB gAB : ℝ →ᵃ[ℝ] ℝ,
      gA.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c ∧
        (Icc a₁ a₂).EqOn f gA ∧
          gB.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c ∧
            (Icc b₁ b₂).EqOn f gB ∧
              gAB.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c ∧
                (Icc (a₁ + b₁) (a₂ + b₂)).EqOn f gAB := by
  let la : ℝ := a₂ - a₁
  let lb : ℝ := b₂ - b₁
  let m : ℝ := min la lb
  let F : ℝ → ℝ := fun x ↦ f (a₁ + x) - f a₁
  let G : ℝ → ℝ := fun x ↦ f (b₁ + x) - f b₁
  let H : ℝ → ℝ := fun x ↦ f (a₁ + b₁ + x) - f (a₁ + b₁)
  have hla_pos : 0 < la := by
    dsimp [la]
    exact sub_pos.mpr ha
  have hlb_pos : 0 < lb := by
    dsimp [lb]
    exact sub_pos.mpr hb
  have hm_pos : 0 < m := by
    dsimp [m]
    exact lt_min hla_pos hlb_pos
  have ha_left : a₁ ∈ Icc a₁ a₂ := by simp [ha.le]
  have hb_left : b₁ ∈ Icc b₁ b₂ := by simp [hb.le]
  have hbase : f a₁ + f b₁ = f (a₁ + b₁) := h_add ha_left hb_left
  have hF_eq_H {x : ℝ} (hx : x ∈ Icc 0 la) : F x = H x := by
    have hax : a₁ + x ∈ Icc a₁ a₂ := by
      constructor
      · linarith [hx.1]
      · have hx_upper : x ≤ a₂ - a₁ := by simpa [la] using hx.2
        linarith
    have hsum := h_add hax hb_left
    -- Compare the translated identity with the base-point identity.
    calc
      F x = f (a₁ + x) - f a₁ := by rfl
      _ = (f (a₁ + x) + f b₁) - (f a₁ + f b₁) := by ring
      _ = f (a₁ + b₁ + x) - f (a₁ + b₁) := by
            rw [hsum, hbase]
            ring_nf
      _ = H x := by rfl
  have hG_eq_H {x : ℝ} (hx : x ∈ Icc 0 lb) : G x = H x := by
    have hbx : b₁ + x ∈ Icc b₁ b₂ := by
      constructor
      · linarith [hx.1]
      · have hx_upper : x ≤ b₂ - b₁ := by simpa [lb] using hx.2
        linarith
    have hsum := h_add ha_left hbx
    -- This is the symmetric translated identity on the `B` side.
    calc
      G x = f (b₁ + x) - f b₁ := by rfl
      _ = (f a₁ + f (b₁ + x)) - (f a₁ + f b₁) := by ring
      _ = f (a₁ + b₁ + x) - f (a₁ + b₁) := by
            rw [hbase, hsum]
            ring_nf
      _ = H x := by rfl
  have hH_add {x y : ℝ} (hx : x ∈ Icc 0 la) (hy : y ∈ Icc 0 lb) :
      H (x + y) = F x + G y := by
    have hax : a₁ + x ∈ Icc a₁ a₂ := by
      constructor
      · linarith [hx.1]
      · have hx_upper : x ≤ a₂ - a₁ := by simpa [la] using hx.2
        linarith
    have hby : b₁ + y ∈ Icc b₁ b₂ := by
      constructor
      · linarith [hy.1]
      · have hy_upper : y ≤ b₂ - b₁ := by simpa [lb] using hy.2
        linarith
    have hsum := h_add hax hby
    -- Subtract the base identity to isolate the translated profiles.
    calc
      H (x + y) = f ((a₁ + x) + (b₁ + y)) - f (a₁ + b₁) := by
            dsimp [H]
            congr 1
            ring
      _ = (f (a₁ + x) + f (b₁ + y)) - (f a₁ + f b₁) := by rw [hsum, hbase]
      _ = (f (a₁ + x) - f a₁) + (f (b₁ + y) - f b₁) := by ring
      _ = F x + G y := by rfl
  have hF_local :
      ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 m → y ∈ Icc 0 m → x + y ∈ Icc 0 m →
        F (x + y) = F x + F y := by
    intro x y hx hy hxy
    have hxA : x ∈ Icc 0 la := ⟨hx.1, le_trans hx.2 (by dsimp [m]; exact min_le_left _ _)⟩
    have hyA : y ∈ Icc 0 la := ⟨hy.1, le_trans hy.2 (by dsimp [m]; exact min_le_left _ _)⟩
    have hyB : y ∈ Icc 0 lb := ⟨hy.1, le_trans hy.2 (by dsimp [m]; exact min_le_right _ _)⟩
    have hxyA : x + y ∈ Icc 0 la := ⟨hxy.1, le_trans hxy.2 (by dsimp [m]; exact min_le_left _ _)⟩
    calc
      F (x + y) = H (x + y) := hF_eq_H hxyA
      _ = F x + G y := hH_add hxA hyB
      _ = F x + F y := by rw [hG_eq_H hyB, ← hF_eq_H hyA]
  have hF_step :
      ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 la → y ∈ Icc 0 m → x + y ∈ Icc 0 la →
        F (x + y) = F x + F y := by
    intro x y hx hy hxy
    have hyA : y ∈ Icc 0 la := ⟨hy.1, le_trans hy.2 (by dsimp [m]; exact min_le_left _ _)⟩
    have hyB : y ∈ Icc 0 lb := ⟨hy.1, le_trans hy.2 (by dsimp [m]; exact min_le_right _ _)⟩
    calc
      F (x + y) = H (x + y) := hF_eq_H hxy
      _ = F x + G y := hH_add hx hyB
      _ = F x + F y := by rw [hG_eq_H hyB, ← hF_eq_H hyA]
  have hG_step :
      ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 lb → y ∈ Icc 0 m → x + y ∈ Icc 0 lb →
        G (x + y) = G x + G y := by
    intro x y hx hy hxy
    have hyA : y ∈ Icc 0 la := ⟨hy.1, le_trans hy.2 (by dsimp [m]; exact min_le_left _ _)⟩
    have hyB : y ∈ Icc 0 lb := ⟨hy.1, le_trans hy.2 (by dsimp [m]; exact min_le_right _ _)⟩
    calc
      G (x + y) = H (x + y) := hG_eq_H hxy
      _ = F y + G x := by simpa [add_comm] using hH_add hyA hx
      _ = G x + G y := by rw [hG_eq_H hyB, ← hF_eq_H hyA, add_comm]
  have hF_bound : ∃ R > 0, ∀ x ∈ Icc 0 m, |F x| ≤ R := by
    have hm_nonneg : 0 ≤ m := hm_pos.le
    rcases (boundedOnBoundedIntervals_iff.mp h_bdd) a₁ (a₁ + m) (by linarith [hm_nonneg]) with
      ⟨M, hM⟩
    have hM_nonneg : 0 ≤ M := by
      have hMa1 : |f a₁| ≤ M := hM _ (by simp [hm_nonneg])
      exact le_trans (abs_nonneg _) hMa1
    refine ⟨|M| + |f a₁| + 1, by positivity, ?_⟩
    intro x hx
    have hax : a₁ + x ∈ Icc a₁ (a₁ + m) := by
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    have hfx : |f (a₁ + x)| ≤ |M| := by
      simpa [abs_of_nonneg hM_nonneg] using hM _ hax
    calc
      |F x| = |f (a₁ + x) - f a₁| := by rfl
      _ ≤ |f (a₁ + x)| + |f a₁| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le (f (a₁ + x)) (-f a₁)
      _ ≤ |M| + |f a₁| + 1 := by linarith
  obtain ⟨c, hF_small⟩ := affine_on_initial_interval_of_bounded_local_add hm_pos hF_local hF_bound
  have hF_all : (Icc 0 la).EqOn F (fun x ↦ c * x) :=
    linear_extension_from_initial_interval hm_pos hF_step hF_small
  have hG_small : (Icc 0 m).EqOn G (fun x ↦ c * x) := by
    intro x hx
    have hxA : x ∈ Icc 0 la := ⟨hx.1, le_trans hx.2 (by dsimp [m]; exact min_le_left _ _)⟩
    have hxB : x ∈ Icc 0 lb := ⟨hx.1, le_trans hx.2 (by dsimp [m]; exact min_le_right _ _)⟩
    rw [hG_eq_H hxB, ← hF_eq_H hxA, hF_small hx]
  have hG_all : (Icc 0 lb).EqOn G (fun x ↦ c * x) :=
    linear_extension_from_initial_interval hm_pos hG_step hG_small
  have hH_all : (Icc 0 (la + lb)).EqOn H (fun x ↦ c * x) := by
    intro z hz
    rcases sum_interval_decomposition_zero hla_pos.le hlb_pos.le hz with ⟨x, hx, y, hy, rfl⟩
    -- Decompose a point of the sum interval into one point from each side.
    calc
      H (x + y) = F x + G y := hH_add hx hy
      _ = c * x + c * y := by rw [hF_all hx, hG_all hy]
      _ = c * (x + y) := by ring
  have hA_intercept : ∃ d : ℝ, (Icc a₁ a₂).EqOn f (fun x ↦ c * x + d) := by
    refine ⟨f a₁ - c * a₁, ?_⟩
    intro a ha_mem
    have hx : a - a₁ ∈ Icc 0 la := by
      constructor
      · linarith [ha_mem.1]
      · dsimp [la]
        linarith [ha_mem.2]
    have hFx := hF_all hx
    -- Rewrite the translated linear formula back on the original interval `A`.
    calc
      f a = f (a₁ + (a - a₁)) := by ring_nf
      _ = c * (a - a₁) + f a₁ := by
            dsimp [F] at hFx
            linarith
      _ = c * a + (f a₁ - c * a₁) := by ring
  have hB_intercept : ∃ d : ℝ, (Icc b₁ b₂).EqOn f (fun x ↦ c * x + d) := by
    refine ⟨f b₁ - c * b₁, ?_⟩
    intro b hb_mem
    have hx : b - b₁ ∈ Icc 0 lb := by
      constructor
      · linarith [hb_mem.1]
      · dsimp [lb]
        linarith [hb_mem.2]
    have hGx := hG_all hx
    -- The same translation argument yields the affine formula on `B`.
    calc
      f b = f (b₁ + (b - b₁)) := by ring_nf
      _ = c * (b - b₁) + f b₁ := by
            dsimp [G] at hGx
            linarith
      _ = c * b + (f b₁ - c * b₁) := by ring
  have hAB_intercept : ∃ d : ℝ, (Icc (a₁ + b₁) (a₂ + b₂)).EqOn f (fun x ↦ c * x + d) := by
    refine ⟨f (a₁ + b₁) - c * (a₁ + b₁), ?_⟩
    intro w hw_mem
    have hz : w - (a₁ + b₁) ∈ Icc 0 (la + lb) := by
      constructor
      · linarith [hw_mem.1]
      · dsimp [la, lb]
        linarith [hw_mem.2]
    have hHz := hH_all hz
    -- Finally translate the linear formula on the shifted sum interval back to `A + B`.
    calc
      f w = f (a₁ + b₁ + (w - (a₁ + b₁))) := by ring_nf
      _ = c * (w - (a₁ + b₁)) + f (a₁ + b₁) := by
            dsimp [H] at hHz
            linarith
      _ = c * w + (f (a₁ + b₁) - c * (a₁ + b₁)) := by ring
  rcases (exists_affineMap_eqOn_iff (f := f) (s := Icc a₁ a₂) (c := c)).2 hA_intercept with
    ⟨gA, hgA, hEqA⟩
  rcases (exists_affineMap_eqOn_iff (f := f) (s := Icc b₁ b₂) (c := c)).2 hB_intercept with
    ⟨gB, hgB, hEqB⟩
  rcases (exists_affineMap_eqOn_iff (f := f) (s := Icc (a₁ + b₁) (a₂ + b₂)) (c := c)).2
    hAB_intercept with ⟨gAB, hgAB, hEqAB⟩
  exact ⟨c, gA, gB, gAB, hgA, hEqA, hgB, hEqB, hgAB, hEqAB⟩

end Lemma626
