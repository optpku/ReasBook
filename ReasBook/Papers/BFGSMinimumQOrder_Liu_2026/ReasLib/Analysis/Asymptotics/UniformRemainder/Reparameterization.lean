module

public import ReasLib.Analysis.Asymptotics.UniformRemainder

public section

open Filter
open scoped Topology

namespace Asymptotics.IsUniformRemainderOn

universe u v w

/-- A filter-tending reparameterization preserves a uniform remainder estimate when the
transformed real-power gauge has its own uniform estimate. -/
theorem comp_tendsto {Θ : Type u} {Ξ : Type v} {E : Type w} [Norm E]
    {R : Θ → ℝ → E} {s : Set Θ} {t : Set Ξ} {C A q p : ℝ}
    (k : Ξ × ℝ → Θ × ℝ) (hR : IsUniformRemainderOn R s C q)
    (hk : Tendsto k (principal t ×ˢ 𝓝 0) (principal s ×ˢ 𝓝 0))
    (hGauge : IsUniformRemainderOn (fun ξ ε ↦ |(k (ξ, ε)).2| ^ q) t A p)
    (hC : 0 ≤ C) :
    IsUniformRemainderOn
      (fun ξ ε ↦ R (k (ξ, ε)).1 (k (ξ, ε)).2) t (C * A) p := by
  -- Pull the original estimate back along `k`, then compare the two gauges.
  refine (isBigOWith_iff
    (fun ξ ε ↦ R (k (ξ, ε)).1 (k (ξ, ε)).2) t (C * A) p).mp ?_
  have hR' := ((isBigOWith_iff R s C q).mpr hR).comp_tendsto hk
  have hGauge' := (isBigOWith_iff (fun ξ ε ↦ |(k (ξ, ε)).2| ^ q) t A p).mpr hGauge
  exact hR'.trans hGauge' hC

end Asymptotics.IsUniformRemainderOn

namespace Asymptotics.IsBigOWith

universe u v

/-- The substitution `b = ε`, `r = ε ^ 2` tends to the mixed product filter when
the `b`-coordinate is restricted to a fixed positive interval. -/
private lemma tendstoWeightedPath {Θ : Type u} {s : Set Θ} {B : ℝ} (hB : 0 < B) :
    Tendsto (fun z : Θ × ℝ ↦ ((z.1, z.2), z.2 ^ 2))
      (principal s ×ˢ 𝓝 0) (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0) := by
  -- Eventual smallness puts the middle coordinate in `[-B, B]`.
  have hmem : ∀ᶠ z : Θ × ℝ in principal s ×ˢ 𝓝 0, (z.1, z.2) ∈ s ×ˢ Set.Icc (-B) B := by
    refine Metric.eventually_prod_nhds_iff.mpr
      ⟨fun θ ↦ θ ∈ s, Filter.eventually_principal.mpr (fun θ hθ ↦ hθ), B, hB, ?_⟩
    intro θ hθ ε hε
    have habs : |ε| < B := by
      simpa only [Real.dist_0_eq_abs] using hε
    exact ⟨hθ, ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩⟩
  -- The squared final coordinate converges to zero independently of that membership fact.
  refine (tendsto_principal.mpr hmem).prodMk ?_
  simpa only [pow_two, zero_mul] using (tendsto_snd.pow 2 :
    Tendsto (fun z : Θ × ℝ ↦ z.2 ^ 2) (principal s ×ˢ 𝓝 0) (𝓝 (0 ^ 2)))

/-- A mixed estimate with gauge `|b| ^ p * |r| ^ q` restricts along
`b = ε`, `r = ε ^ 2` to a uniform remainder of order `p + 2 * q`. -/
theorem weightedPath {Θ : Type u} {E : Type v} [Norm E]
    {R : Θ → ℝ → ℝ → E} {s : Set Θ} {B C p q : ℝ}
    (hR : IsBigOWith C (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0)
      (fun z : (Θ × ℝ) × ℝ ↦ R z.1.1 z.1.2 z.2)
      (fun z ↦ |z.1.2| ^ p * |z.2| ^ q))
    (hB : 0 < B) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    IsUniformRemainderOn (fun θ ε ↦ R θ ε (ε ^ 2)) s C (p + 2 * q) := by
  -- Pull the mixed estimate back along the single weighted path.
  refine (Asymptotics.IsUniformRemainderOn.isBigOWith_iff
    (fun θ ε ↦ R θ ε (ε ^ 2)) s C (p + 2 * q)).mp ?_
  have hpull := hR.comp_tendsto (tendstoWeightedPath hB)
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  -- Normalize the squared-coordinate power and then add the two exponents.
  have hGauge (z : Θ × ℝ) :
      |z.2| ^ p * |z.2 ^ 2| ^ q = |z.2| ^ (p + 2 * q) := by
    rw [abs_pow, ← Real.rpow_natCast_mul (abs_nonneg z.2) 2 q]
    norm_num only
    rw [← Real.rpow_add_of_nonneg (abs_nonneg z.2) hp (mul_nonneg htwo hq)]
  exact hpull.congr_right hGauge

/-- A mixed cubic estimate in `r` has uniform order six along
`b = ε`, `r = ε ^ 2`. -/
theorem weightedPathCubic {Θ : Type u} {E : Type v} [Norm E]
    {R : Θ → ℝ → ℝ → E} {s : Set Θ} {B C : ℝ}
    (hR : IsBigOWith C (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0)
      (fun z : (Θ × ℝ) × ℝ ↦ R z.1.1 z.1.2 z.2)
      (fun z ↦ |z.2| ^ (3 : ℝ)))
    (hB : 0 < B) :
    IsUniformRemainderOn (fun θ ε ↦ R θ ε (ε ^ 2)) s C 6 := by
  -- Insert the harmless order-zero factor for `b` and specialize the general path result.
  have hGauge (z : (Θ × ℝ) × ℝ) :
      |z.2| ^ (3 : ℝ) = |z.1.2| ^ (0 : ℝ) * |z.2| ^ (3 : ℝ) := by
    simp only [Real.rpow_zero, one_mul]
  have hmixed : IsBigOWith C (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0)
      (fun z : (Θ × ℝ) × ℝ ↦ R z.1.1 z.1.2 z.2)
      (fun z ↦ |z.1.2| ^ (0 : ℝ) * |z.2| ^ (3 : ℝ)) :=
    hR.congr_right hGauge
  have hp : (0 : ℝ) ≤ 0 := le_rfl
  have hq : (0 : ℝ) ≤ 3 := by norm_num
  have hpath := weightedPath hmixed hB hp hq
  norm_num at hpath
  exact hpath

/-- A mixed estimate with gauge `|b| * |r| ^ 3` has uniform order seven along
`b = ε`, `r = ε ^ 2`. -/
theorem weightedPathLinearCubic {Θ : Type u} {E : Type v} [Norm E]
    {R : Θ → ℝ → ℝ → E} {s : Set Θ} {B C : ℝ}
    (hR : IsBigOWith C (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0)
      (fun z : (Θ × ℝ) × ℝ ↦ R z.1.1 z.1.2 z.2)
      (fun z ↦ |z.1.2| * |z.2| ^ (3 : ℝ)))
    (hB : 0 < B) :
    IsUniformRemainderOn (fun θ ε ↦ R θ ε (ε ^ 2)) s C 7 := by
  -- Rewrite the linear factor as real power one and specialize the general path result.
  have hGauge (z : (Θ × ℝ) × ℝ) :
      |z.1.2| * |z.2| ^ (3 : ℝ) =
        |z.1.2| ^ (1 : ℝ) * |z.2| ^ (3 : ℝ) := by
    simp only [Real.rpow_one]
  have hmixed : IsBigOWith C (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0)
      (fun z : (Θ × ℝ) × ℝ ↦ R z.1.1 z.1.2 z.2)
      (fun z ↦ |z.1.2| ^ (1 : ℝ) * |z.2| ^ (3 : ℝ)) :=
    hR.congr_right hGauge
  have hp : (0 : ℝ) ≤ 1 := by norm_num
  have hq : (0 : ℝ) ≤ 3 := by norm_num
  have hpath := weightedPath hmixed hB hp hq
  norm_num at hpath
  exact hpath

end Asymptotics.IsBigOWith
