module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

open Filter
open scoped Topology

namespace Asymptotics

universe u v w

variable {Θ : Type u} {E : Type v} [Norm E]

/-- `IsUniformRemainderOn R s C q` means that one positive radius works for every
parameter `θ ∈ s` in the estimate `‖R θ ε‖ ≤ C * |ε| ^ q`. -/
def IsUniformRemainderOn (R : Θ → ℝ → E) (s : Set Θ) (C q : ℝ) : Prop :=
  ∃ δ > 0, ∀ θ ∈ s, ∀ ε : ℝ, |ε| < δ → ‖R θ ε‖ ≤ C * |ε| ^ q

namespace IsUniformRemainderOn

/-- Build a uniform remainder estimate from one positive radius and its
pointwise bound. -/
theorem of_bound {R : Θ → ℝ → E} {s : Set Θ} {C q δ : ℝ}
    (hδ : 0 < δ)
    (hbound : ∀ θ ∈ s, ∀ ε : ℝ, |ε| < δ → ‖R θ ε‖ ≤ C * |ε| ^ q) :
    IsUniformRemainderOn R s C q := by
  exact ⟨δ, hδ, hbound⟩

/-- A uniform remainder estimate supplies a common positive radius for its
pointwise bounds. -/
theorem exists_bound {R : Θ → ℝ → E} {s : Set Θ} {C q : ℝ}
    (h : IsUniformRemainderOn R s C q) :
    ∃ δ > 0, ∀ θ ∈ s, ∀ ε : ℝ, |ε| < δ →
      ‖R θ ε‖ ≤ C * |ε| ^ q := by
  exact h

/-- The explicit common-radius estimate is equivalent to fixed-coefficient big-O on
`Filter.principal s ×ˢ 𝓝 0`. -/
theorem isBigOWith_iff (R : Θ → ℝ → E) (s : Set Θ) (C q : ℝ) :
    IsBigOWith C (Filter.principal s ×ˢ 𝓝 0) (fun z : Θ × ℝ ↦ R z.1 z.2)
        (fun z : Θ × ℝ ↦ |z.2| ^ q) ↔ IsUniformRemainderOn R s C q := by
  -- Expose the eventual norm inequality and then extract its common product-neighborhood radius.
  rw [Asymptotics.isBigOWith_iff]
  constructor
  · intro h
    obtain ⟨p, hp, δ, hδ, hbound⟩ := Metric.eventually_prod_nhds_iff.mp h
    refine ⟨δ, hδ, ?_⟩
    intro θ hθ ε hε
    have hpθ : p θ := (Filter.eventually_principal.mp hp) θ hθ
    have hdist : dist ε 0 < δ := by
      simpa only [Real.dist_0_eq_abs] using hε
    have hnorm := hbound hpθ hdist
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg ε) q)] using hnorm
  · rintro ⟨δ, hδ, hbound⟩
    -- Use set membership as the first-factor predicate and the supplied radius for the second.
    refine Metric.eventually_prod_nhds_iff.mpr
      ⟨fun θ ↦ θ ∈ s, Filter.eventually_principal.mpr (fun θ hθ ↦ hθ), δ, hδ, ?_⟩
    intro θ hθ ε hε
    have habs : |ε| < δ := by
      simpa only [Real.dist_0_eq_abs] using hε
    have hnorm := hbound θ hθ ε habs
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg ε) q)] using hnorm

/-- Ordinary big-O on the product filter is equivalent to the existence of a coefficient
for an explicit uniform remainder estimate. -/
theorem isBigO_iff (R : Θ → ℝ → E) (s : Set Θ) (q : ℝ) :
    (fun z : Θ × ℝ ↦ R z.1 z.2) =O[Filter.principal s ×ˢ 𝓝 0]
        (fun z : Θ × ℝ ↦ |z.2| ^ q) ↔
      ∃ C : ℝ, IsUniformRemainderOn R s C q := by
  -- Transport the existential coefficient through the fixed-coefficient equivalence.
  rw [Asymptotics.isBigO_iff_isBigOWith]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (isBigOWith_iff R s C q).mp hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (isBigOWith_iff R s C q).mpr hC⟩

/-- Little-o on the product filter is equivalent to uniform remainder estimates with every
positive coefficient. -/
theorem isLittleO_iff (R : Θ → ℝ → E) (s : Set Θ) (q : ℝ) :
    (fun z : Θ × ℝ ↦ R z.1 z.2) =o[Filter.principal s ×ˢ 𝓝 0]
        (fun z : Θ × ℝ ↦ |z.2| ^ q) ↔
      ∀ ⦃C : ℝ⦄, 0 < C → IsUniformRemainderOn R s C q := by
  -- Transport every positive coefficient through the same fixed-coefficient bridge.
  rw [Asymptotics.isLittleO_iff_forall_isBigOWith]
  constructor
  · intro h C hC
    exact (isBigOWith_iff R s C q).mp (h hC)
  · intro h C hC
    exact (isBigOWith_iff R s C q).mpr (h hC)

end IsUniformRemainderOn

/-- The tail supremum of the normalized values of `R` on `s` at nonzero increments
whose absolute value is at most `η`, with zero included. -/
noncomputable def uniformRemainderModulus (R : Θ → ℝ → E) (s : Set Θ) (q η : ℝ) : ℝ :=
  sSup (insert 0 {c : ℝ | ∃ θ ∈ s, ∃ ε : ℝ,
    0 < |ε| ∧ |ε| ≤ η ∧ c = ‖R θ ε‖ / |ε| ^ q})

/-- A uniform remainder modulus is locally nonnegative and monotone, tends to zero
from the right, and uniformly bounds the normalized remainder. -/
def IsUniformRemainderModulusOn (R : Θ → ℝ → E) (s : Set Θ) (q η₀ : ℝ)
    (ω : ℝ → ℝ) : Prop :=
  (∀ η ∈ Set.Ioc 0 η₀, 0 ≤ ω η) ∧
    MonotoneOn ω (Set.Ioc 0 η₀) ∧
    Tendsto ω (𝓝[>] 0) (𝓝 0) ∧
    ∀ θ ∈ s, ∀ η ∈ Set.Ioc 0 η₀, ∀ ε : ℝ,
      0 < |ε| → |ε| ≤ η → ‖R θ ε‖ ≤ ω η * |ε| ^ q

namespace IsUniformRemainderModulusOn

/-- The nonnegativity, monotonicity, convergence, and uniform bound conditions
defining a uniform remainder modulus. -/
theorem spec (R : Θ → ℝ → E) (s : Set Θ) (q η₀ : ℝ) (ω : ℝ → ℝ) :
    IsUniformRemainderModulusOn R s q η₀ ω ↔
      (∀ η ∈ Set.Ioc 0 η₀, 0 ≤ ω η) ∧
        MonotoneOn ω (Set.Ioc 0 η₀) ∧
        Tendsto ω (𝓝[>] 0) (𝓝 0) ∧
        ∀ θ ∈ s, ∀ η ∈ Set.Ioc 0 η₀, ∀ ε : ℝ,
          0 < |ε| → |ε| ≤ η → ‖R θ ε‖ ≤ ω η * |ε| ^ q := by
  -- Unfolding exposes exactly the four defining properties of the modulus.
  rfl

/-- A uniform remainder modulus is nonnegative on its interval of validity. -/
theorem nonneg {R : Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ} {ω : ℝ → ℝ}
    (hω : IsUniformRemainderModulusOn R s q η₀ ω) :
    ∀ η ∈ Set.Ioc 0 η₀, 0 ≤ ω η :=
  (spec R s q η₀ ω).mp hω |>.1

/-- A uniform remainder modulus is monotone on its interval of validity. -/
theorem monotoneOn {R : Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ} {ω : ℝ → ℝ}
    (hω : IsUniformRemainderModulusOn R s q η₀ ω) :
    MonotoneOn ω (Set.Ioc 0 η₀) :=
  (spec R s q η₀ ω).mp hω |>.2.1

/-- A uniform remainder modulus tends to zero from the right. -/
theorem tendsto_zero {R : Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ} {ω : ℝ → ℝ}
    (hω : IsUniformRemainderModulusOn R s q η₀ ω) :
    Tendsto ω (𝓝[>] 0) (𝓝 0) :=
  (spec R s q η₀ ω).mp hω |>.2.2.1

/-- A uniform remainder modulus bounds the remainder at every admissible parameter,
scale, and nonzero increment. -/
theorem bound {R : Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ} {ω : ℝ → ℝ}
    (hω : IsUniformRemainderModulusOn R s q η₀ ω) {θ : Θ} {η ε : ℝ}
    (hθ : θ ∈ s) (hη : η ∈ Set.Ioc 0 η₀) (hε : 0 < |ε|) (hεη : |ε| ≤ η) :
    ‖R θ ε‖ ≤ ω η * |ε| ^ q := by
  -- Project the pointwise estimate from the defining specification.
  exact hω.2.2.2 θ hθ η hη ε hε hεη

/-- An explicit coefficient bound controls the normalized tail supremum, which is
nonnegative and in turn bounds every normalized value at the same scale. -/
private lemma uniformRemainderModulus_specOfBound (R : Θ → ℝ → E) (s : Set Θ)
    (q η C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ θ ∈ s, ∀ ε : ℝ, 0 < |ε| → |ε| ≤ η →
      ‖R θ ε‖ ≤ C * |ε| ^ q) :
    BddAbove (insert 0 {c : ℝ | ∃ θ ∈ s, ∃ ε : ℝ,
      0 < |ε| ∧ |ε| ≤ η ∧ c = ‖R θ ε‖ / |ε| ^ q}) ∧
      0 ≤ uniformRemainderModulus R s q η ∧
      uniformRemainderModulus R s q η ≤ C ∧
      ∀ θ ∈ s, ∀ ε : ℝ, 0 < |ε| → |ε| ≤ η →
        ‖R θ ε‖ ≤ uniformRemainderModulus R s q η * |ε| ^ q := by
  -- Every member of the defining set is bounded above by the supplied coefficient.
  have hupper : ∀ c ∈ insert 0 {d : ℝ | ∃ θ ∈ s, ∃ ε : ℝ,
      0 < |ε| ∧ |ε| ≤ η ∧ d = ‖R θ ε‖ / |ε| ^ q}, c ≤ C := by
    intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact hC
    · rcases hc with ⟨θ, hθ, ε, hε, hεη, rfl⟩
      have hpow : 0 < |ε| ^ q := Real.rpow_pos_of_pos hε q
      exact (div_le_iff₀ hpow).2 (hbound θ hθ ε hε hεη)
  have hbdd : BddAbove (insert 0 {c : ℝ | ∃ θ ∈ s, ∃ ε : ℝ,
      0 < |ε| ∧ |ε| ≤ η ∧ c = ‖R θ ε‖ / |ε| ^ q}) := ⟨C, hupper⟩
  have hnonempty : (insert 0 {c : ℝ | ∃ θ ∈ s, ∃ ε : ℝ,
      0 < |ε| ∧ |ε| ≤ η ∧ c = ‖R θ ε‖ / |ε| ^ q}).Nonempty :=
    ⟨0, Set.mem_insert 0 _⟩
  refine ⟨hbdd, ?_, ?_, ?_⟩
  · -- The inserted zero witnesses nonnegativity of the supremum.
    rw [uniformRemainderModulus]
    exact le_csSup hbdd (Set.mem_insert 0 _)
  · -- The common upper bound also bounds the supremum itself.
    rw [uniformRemainderModulus]
    exact csSup_le hnonempty hupper
  · intro θ hθ ε hε hεη
    have hpow : 0 < |ε| ^ q := Real.rpow_pos_of_pos hε q
    have hnormalized : ‖R θ ε‖ / |ε| ^ q ≤ uniformRemainderModulus R s q η := by
      rw [uniformRemainderModulus]
      apply le_csSup hbdd
      exact Set.mem_insert_iff.mpr (Or.inr ⟨θ, hθ, ε, hε, hεη, rfl⟩)
    -- Multiplying back by the positive power recovers the remainder estimate.
    exact (div_le_iff₀ hpow).1 hnormalized

/-- A uniformly little-o remainder has a positive radius on which its tail-supremum
function is a uniform remainder modulus. -/
theorem of_isLittleO (R : Θ → ℝ → E) (s : Set Θ) (q : ℝ)
    (hR : (fun z : Θ × ℝ ↦ R z.1 z.2) =o[Filter.principal s ×ˢ 𝓝 0]
      (fun z : Θ × ℝ ↦ |z.2| ^ q)) :
    ∃ η₀ > 0, IsUniformRemainderModulusOn R s q η₀
      (uniformRemainderModulus R s q) := by
  -- Use the coefficient-one estimate to fix one common positive working radius.
  have hOnePos : (0 : ℝ) < 1 := by norm_num
  have hOne := (IsUniformRemainderOn.isLittleO_iff R s q).mp hR hOnePos
  have hOneExplicit : ∃ δ > 0, ∀ θ ∈ s, ∀ ε : ℝ,
      |ε| < δ → ‖R θ ε‖ ≤ 1 * |ε| ^ q := hOne
  obtain ⟨δ, hδ, hδbound⟩ := hOneExplicit
  have hhalfδ : δ / 2 < δ := by linarith
  have hlocalBound : ∀ η ≤ δ / 2, ∀ θ ∈ s, ∀ ε : ℝ,
      0 < |ε| → |ε| ≤ η → ‖R θ ε‖ ≤ 1 * |ε| ^ q := by
    intro η hη θ hθ ε _ hεη
    exact hδbound θ hθ ε (hεη.trans_lt (hη.trans_lt hhalfδ))
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  refine (spec R s q (δ / 2) (uniformRemainderModulus R s q)).mpr
    ⟨?_, ?_, ?_, ?_⟩
  · intro η hη
    -- Zero belongs to the normalized tail set, so its supremum is nonnegative.
    exact (uniformRemainderModulus_specOfBound R s q η 1 hOnePos.le
      (hlocalBound η hη.2)).2.1
  · intro η₁ hη₁ η₂ hη₂ hη₁₂
    -- Inclusion of the smaller tail set into the larger one gives monotonicity.
    have hspec₂ := uniformRemainderModulus_specOfBound R s q η₂ 1 hOnePos.le
      (hlocalBound η₂ hη₂.2)
    rw [uniformRemainderModulus, uniformRemainderModulus]
    apply csSup_le_csSup hspec₂.1
    · exact ⟨0, Set.mem_insert 0 _⟩
    · intro c hc
      rcases Set.mem_insert_iff.mp hc with rfl | hc
      · exact Set.mem_insert 0 _
      · rcases hc with ⟨θ, hθ, ε, hε, hεη, hc⟩
        exact Set.mem_insert_iff.mpr
          (Or.inr ⟨θ, hθ, ε, hε, hεη.trans hη₁₂, hc⟩)
  · -- Every positive target coefficient supplies a right-neighborhood on which
    -- the tail supremum is smaller than that target.
    refine Metric.tendsto_nhds.mpr ?_
    intro ρ hρ
    have hρhalf : 0 < ρ / 2 := half_pos hρ
    have hSmall := (IsUniformRemainderOn.isLittleO_iff R s q).mp hR hρhalf
    have hSmallExplicit : ∃ δρ > 0, ∀ θ ∈ s, ∀ ε : ℝ,
        |ε| < δρ → ‖R θ ε‖ ≤ (ρ / 2) * |ε| ^ q := hSmall
    obtain ⟨δρ, hδρ, hδρbound⟩ := hSmallExplicit
    filter_upwards [Ioo_mem_nhdsGT hδρ] with η hη
    have hboundρ : ∀ θ ∈ s, ∀ ε : ℝ, 0 < |ε| → |ε| ≤ η →
        ‖R θ ε‖ ≤ (ρ / 2) * |ε| ^ q := by
      intro θ hθ ε _ hεη
      exact hδρbound θ hθ ε (hεη.trans_lt hη.2)
    have hspecρ := uniformRemainderModulus_specOfBound R s q η (ρ / 2)
      hρhalf.le hboundρ
    rw [Real.dist_0_eq_abs, abs_of_nonneg hspecρ.2.1]
    exact hspecρ.2.2.1.trans_lt (half_lt_self hρ)
  · intro θ hθ η hη ε hε hεη
    -- The supremum interface turns membership of the normalized value into the final bound.
    exact (uniformRemainderModulus_specOfBound R s q η 1 hOnePos.le
      (hlocalBound η hη.2)).2.2.2 θ hθ ε hε hεη

/-- A uniform remainder modulus simultaneously bounds every indexed family whose
positive increments lie below an admissible common scale. -/
theorem bound_orbits {R : Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ} {ω : ℝ → ℝ}
    (hω : IsUniformRemainderModulusOn R s q η₀ ω) {ι : Type w}
    (p : ι → ℕ → Θ) (ε : ι → ℕ → ℝ) (ε₀ : ι → ℝ) (η : ℝ)
    (hp : ∀ i j, p i j ∈ s)
    (hε : ∀ i j, 0 < ε i j ∧ ε i j ≤ ε₀ i)
    (hε₀ : ∀ i, ε₀ i ≤ η) (hη : η ∈ Set.Ioc 0 η₀) :
    ∀ i j, ‖R (p i j) (ε i j)‖ ≤ ω η * |ε i j| ^ q := by
  intro i j
  -- Positivity removes the absolute value, and the two scale inequalities compose.
  have hεpos : 0 < |ε i j| := by
    simpa only [abs_of_pos (hε i j).1] using (hε i j).1
  have hεle : |ε i j| ≤ η := by
    rw [abs_of_pos (hε i j).1]
    exact (hε i j).2.trans (hε₀ i)
  exact bound hω (hp i j) hη hεpos hεle

end IsUniformRemainderModulusOn

end Asymptotics
