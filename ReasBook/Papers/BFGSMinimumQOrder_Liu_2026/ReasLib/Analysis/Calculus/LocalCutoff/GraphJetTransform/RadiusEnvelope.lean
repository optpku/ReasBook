module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

open Finset

namespace LocalCutoff.GraphTransform

/-- Helper for Infrastructure I.16a: iterating a normalized affine radius
recurrence accumulates a finite geometric forcing budget. -/
private theorem normalizedRadiusRecurrence_iterate
    {G : ℝ → ℝ} {q c e δ x : ℝ}
    (hq : 0 ≤ q)
    (hrec : ∀ y, 0 < y → y < δ → G y ≤ q * G (c * y) + e)
    (n : ℕ)
    (horbit : ∀ j < n, 0 < c ^ j * x ∧ c ^ j * x < δ) :
    G x ≤ q ^ n * G (c ^ n * x) + e * ∑ j ∈ range n, q ^ j := by
  -- Induct on the orbit length, applying the recurrence only at its last point.
  induction n with
  | zero => simp
  | succ n ih =>
      have hprefix : ∀ j < n, 0 < c ^ j * x ∧ c ^ j * x < δ := by
        intro j hj
        exact horbit j (hj.trans (Nat.lt_succ_self n))
      have hstep := hrec (c ^ n * x) (horbit n (Nat.lt_succ_self n)).1
        (horbit n (Nat.lt_succ_self n)).2
      have hscaled := mul_le_mul_of_nonneg_left hstep (pow_nonneg hq n)
      have hcarg : c * (c ^ n * x) = c ^ (n + 1) * x := by
        rw [pow_succ]
        ring
      calc
        G x ≤ q ^ n * G (c ^ n * x) + e * ∑ j ∈ range n, q ^ j := ih hprefix
        _ ≤ q ^ n * (q * G (c * (c ^ n * x)) + e) +
              e * ∑ j ∈ range n, q ^ j := add_le_add hscaled le_rfl
        _ = q ^ (n + 1) * G (c ^ (n + 1) * x) +
              e * ∑ j ∈ range (n + 1), q ^ j := by
          rw [sum_range_succ, pow_succ, ← hcarg]
          ring

/-- Helper for Infrastructure I.16a: an expanding geometric orbit starting
below `δ / c` has a first point in the annulus from `δ / c` to `δ`. -/
private theorem exists_geometric_orbit_mem_annulus
    {c δ x : ℝ} (hc : 1 < c) (hδ : 0 < δ) (hx : 0 < x)
    (hsmall : x < δ / c) :
    ∃ n : ℕ, δ / c ≤ c ^ n * x ∧ c ^ n * x < δ := by
  have htarget_pos : 0 < (δ / c) / x := div_pos (div_pos hδ (zero_lt_one.trans hc)) hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((δ / c) / x) hc
  have hexists : ∃ n : ℕ, δ / c ≤ c ^ n * x := by
    refine ⟨n, ?_⟩
    have hmul := mul_lt_mul_of_pos_right hn hx
    calc
      δ / c = ((δ / c) / x) * x := by field_simp
      _ ≤ c ^ n * x := hmul.le
  let n₀ := Nat.find hexists
  have hn₀_lower : δ / c ≤ c ^ n₀ * x := Nat.find_spec hexists
  have hn₀_ne : n₀ ≠ 0 := by
    intro hzero
    have hlower := hn₀_lower
    rw [hzero, pow_zero, one_mul] at hlower
    exact (not_le_of_gt hsmall) hlower
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn₀_ne
  have hk_min : ¬δ / c ≤ c ^ k * x := by
    intro hk_lower
    have hn₀_le := Nat.find_min' hexists hk_lower
    change n₀ ≤ k at hn₀_le
    rw [hk] at hn₀_le
    exact (Nat.not_succ_le_self k) hn₀_le
  have hk_lt : c ^ k * x < δ / c := lt_of_not_ge hk_min
  refine ⟨n₀, hn₀_lower, ?_⟩
  rw [hk, pow_succ]
  calc
    c ^ k * c * x = c * (c ^ k * x) := by ring
    _ < c * (δ / c) := mul_lt_mul_of_pos_left hk_lt (zero_lt_one.trans hc)
    _ = δ := by field_simp

/-- Infrastructure I.16a: a monotone radius envelope with a locally bounded affine
recurrence is sublinear at zero when the weighted transport factor is below
one. -/
theorem radiusEnvelope_sublinear_of_recurrence
    (F : ℝ → ℝ) (p c : ℝ)
    (hmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hp : 0 ≤ p) (hp_lt : p < 1) (hc : 0 < c) (hpc : p * c < 1)
    (hbounded : ∃ δ > 0, ∃ M ≥ 0, ∀ x, 0 ≤ x → x < δ → F x ≤ M)
    (hrec : ∀ e > 0, ∃ δ > 0, ∀ x, 0 < x → x < δ →
      F x ≤ p * F (c * x) + e * x) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x → x < δ → F x ≤ ε * x := by
  intro ε hε
  by_cases hc_one : c ≤ 1
  · -- For a nonexpanding radius, monotonicity absorbs the recursive term at once.
    have he_pos : 0 < ε * (1 - p) := mul_pos hε (sub_pos.mpr hp_lt)
    obtain ⟨δ, hδ, hδrec⟩ := hrec (ε * (1 - p)) he_pos
    refine ⟨δ, hδ, ?_⟩
    intro x hx hxδ
    have hcx_nonneg : 0 ≤ c * x := mul_nonneg hc.le hx.le
    have hcx_le : c * x ≤ x := by nlinarith
    have hFx := (hδrec x hx hxδ).trans <|
      add_le_add (mul_le_mul_of_nonneg_left
        (hmono hcx_nonneg hcx_le) hp) le_rfl
    nlinarith
  · -- For an expanding radius, stop at the first point in a fixed annulus.
    have hc_one_lt : 1 < c := lt_of_not_ge hc_one
    have hq_nonneg : 0 ≤ p * c := mul_nonneg hp hc.le
    obtain ⟨δb, hδb, M, hM, hMbound⟩ := hbounded
    have he_pos : 0 < ε * (1 - p * c) / 2 := by positivity
    obtain ⟨δr, hδr, hδrec⟩ := hrec (ε * (1 - p * c) / 2) he_pos
    let δ₀ := min δb δr
    have hδ₀ : 0 < δ₀ := lt_min hδb hδr
    let A := M * c / δ₀
    have hA : 0 ≤ A := div_nonneg (mul_nonneg hM hc.le) hδ₀.le
    have hA_plus_one_pos : 0 < A + 1 := by linarith
    have htarget : 0 < (ε / 2) / (A + 1) :=
      div_pos (half_pos hε) hA_plus_one_pos
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one htarget hpc
    let δ := min (δ₀ / c) (δ₀ / c ^ (N + 1))
    have hδ : 0 < δ := lt_min (div_pos hδ₀ hc)
      (div_pos hδ₀ (pow_pos hc _))
    refine ⟨δ, hδ, ?_⟩
    intro x hx hxδ
    have hx_annulus : x < δ₀ / c := hxδ.trans_le (min_le_left _ _)
    obtain ⟨n, hn_lower, hn_upper⟩ :=
      exists_geometric_orbit_mem_annulus hc_one_lt hδ₀ hx hx_annulus
    have hNn : N ≤ n := by
      by_contra hnot
      have hnN : n < N := Nat.lt_of_not_ge hnot
      have hpow_le : c ^ n ≤ c ^ N := pow_le_pow_right₀ hc_one_lt.le hnN.le
      have hx_small : x < δ₀ / c ^ (N + 1) :=
        hxδ.trans_le (min_le_right _ _)
      have hmul := mul_lt_mul_of_pos_left hx_small (pow_pos hc n)
      have hterminal_lt : c ^ n * x < δ₀ / c := by
        calc
          c ^ n * x < c ^ n * (δ₀ / c ^ (N + 1)) := hmul
          _ ≤ c ^ N * (δ₀ / c ^ (N + 1)) := by
            exact mul_le_mul_of_nonneg_right hpow_le
              (div_nonneg hδ₀.le (pow_nonneg hc.le _))
          _ = δ₀ / c := by
            rw [pow_succ]
            field_simp
      exact (not_lt_of_ge hn_lower) hterminal_lt
    let G : ℝ → ℝ := fun y ↦ F y / y
    have hGrec : ∀ y, 0 < y → y < δ₀ →
        G y ≤ (p * c) * G (c * y) + ε * (1 - p * c) / 2 := by
      intro y hy hyδ₀
      have hyδr : y < δr := hyδ₀.trans_le (min_le_right _ _)
      have hraw := hδrec y hy hyδr
      have hcy : 0 < c * y := mul_pos hc hy
      dsimp only [G]
      calc
        F y / y ≤ (p * F (c * y) + ε * (1 - p * c) / 2 * y) / y :=
          div_le_div_of_nonneg_right hraw hy.le
        _ = (p * c) * (F (c * y) / (c * y)) + ε * (1 - p * c) / 2 := by
          field_simp
    have horbit : ∀ j < n, 0 < c ^ j * x ∧ c ^ j * x < δ₀ := by
      intro j hj
      have hj_nonneg : 0 ≤ c ^ j := pow_nonneg hc.le j
      have hjn : c ^ j ≤ c ^ n := pow_le_pow_right₀ hc_one_lt.le hj.le
      refine ⟨mul_pos (pow_pos hc j) hx, ?_⟩
      exact (mul_le_mul_of_nonneg_right hjn hx.le).trans_lt hn_upper
    have hiter := normalizedRadiusRecurrence_iterate hq_nonneg hGrec n horbit
    have hterminal_nonneg : 0 ≤ c ^ n * x := (mul_pos (pow_pos hc n) hx).le
    have hterminal_bdd : F (c ^ n * x) ≤ M :=
      hMbound _ hterminal_nonneg (hn_upper.trans_le (min_le_left _ _))
    have hGterminal : G (c ^ n * x) ≤ A := by
      dsimp only [G, A]
      calc
        F (c ^ n * x) / (c ^ n * x) ≤ M / (c ^ n * x) :=
          div_le_div_of_nonneg_right hterminal_bdd hterminal_nonneg
        _ ≤ M / (δ₀ / c) := by
          exact div_le_div_of_nonneg_left hM (div_pos hδ₀ hc) hn_lower
        _ = M * c / δ₀ := by field_simp
    have hqpow : (p * c) ^ n ≤ (p * c) ^ N :=
      pow_le_pow_of_le_one hq_nonneg hpc.le hNn
    have hgeom : (∑ j ∈ range n, (p * c) ^ j) ≤ 1 / (1 - p * c) := by
      apply (le_div_iff₀ (sub_pos.mpr hpc)).mpr
      rw [geom_sum_mul_neg]
      exact sub_le_self 1 (pow_nonneg hq_nonneg n)
    have hprincipal : (p * c) ^ n * G (c ^ n * x) ≤ ε / 2 := by
      calc
        (p * c) ^ n * G (c ^ n * x) ≤ (p * c) ^ n * A :=
          mul_le_mul_of_nonneg_left hGterminal (pow_nonneg hq_nonneg n)
        _ ≤ (p * c) ^ N * A := mul_le_mul_of_nonneg_right hqpow hA
        _ ≤ ((ε / 2) / (A + 1)) * A :=
          mul_le_mul_of_nonneg_right hN.le hA
        _ ≤ ε / 2 := le_of_lt <| by
          have hA_lt : A < A + 1 := lt_add_one A
          calc
            (ε / 2 / (A + 1)) * A < (ε / 2 / (A + 1)) * (A + 1) :=
              mul_lt_mul_of_pos_left hA_lt htarget
            _ = ε / 2 := by field_simp
    have hforcing :
        (ε * (1 - p * c) / 2) * ∑ j ∈ range n, (p * c) ^ j ≤ ε / 2 := by
      calc
        _ ≤ (ε * (1 - p * c) / 2) * (1 / (1 - p * c)) :=
          mul_le_mul_of_nonneg_left hgeom he_pos.le
        _ = ε / 2 := by
          field_simp [ne_of_gt (sub_pos.mpr hpc)]
    have hGx : G x ≤ ε := hiter.trans <| by nlinarith
    dsimp only [G] at hGx
    exact (div_le_iff₀ hx).mp hGx

end LocalCutoff.GraphTransform
