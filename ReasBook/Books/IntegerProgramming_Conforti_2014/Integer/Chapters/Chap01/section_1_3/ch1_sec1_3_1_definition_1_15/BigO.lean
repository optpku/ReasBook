module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Lattice.Fold

public section

namespace Asymptotics

private theorem eventually_atTop_unboundedSubtype_iff
    {S : Set NNReal} (hS : Set.Unbounded (· ≤ ·) S) {p : S → Prop} :
    (∀ᶠ x : S in Filter.atTop, p x) ↔ ∃ x₀ : S, ∀ x : S, x₀ < x → p x := by
  have hcomap : Filter.comap ((↑) : S → NNReal) Filter.atTop = Filter.atTop :=
    Filter.comap_embedding_atTop (fun _ _ ↦ Iff.rfl) fun a ↦ by
      obtain ⟨b, hbS, hab⟩ := hS a
      exact ⟨⟨b, hbS⟩, le_of_not_ge hab⟩
  rw [← hcomap, Filter.eventually_comap, Filter.eventually_atTop]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨x₀, hx₀S, hax₀⟩ := hS a
    refine ⟨⟨x₀, hx₀S⟩, fun x hx ↦ ?_⟩
    exact ha x (le_of_lt ((lt_of_not_ge hax₀).trans hx)) x rfl
  · rintro ⟨x₀, hx₀⟩
    obtain ⟨a, haS, hx₀a⟩ := hS x₀.1
    refine ⟨a, fun y hy x hxy ↦ ?_⟩
    subst hxy
    exact hx₀ x ((lt_of_not_ge hx₀a).trans_le hy)

/-- Definition 1.15 (1). For functions `f g : S → NNReal` on an unbounded subset `S ⊆ NNReal`,
the textbook threshold formulation of `f(x) = O(g(x))` is equivalent to the canonical
real-valued `=O[Filter.atTop]` statement obtained by coercing `f` and `g` to `ℝ`. -/
theorem isBigO_nnrealSubtype_iff
    {S : Set NNReal} (hS : Set.Unbounded (· ≤ ·) S) {f g : S → NNReal} :
    (fun x ↦ (f x : ℝ)) =O[Filter.atTop] (fun x ↦ (g x : ℝ)) ↔
      ∃ M > 0, ∃ x₀ : S, ∀ x : S, x₀ < x → f x ≤ M * g x := by
  rw [isBigO_iff']
  constructor
  · rintro ⟨M, hM, hbound⟩
    have hbound' : ∀ᶠ x : S in Filter.atTop, f x ≤ Real.toNNReal M * g x := by
      filter_upwards [hbound] with x hx
      have hx' : (f x : ℝ) ≤ M * (g x : ℝ) := by
        simpa [Real.norm_of_nonneg] using hx
      exact_mod_cast (show (f x : ℝ) ≤ ((Real.toNNReal M * g x : NNReal) : ℝ) by
        simpa [NNReal.coe_mul, Real.coe_toNNReal M hM.le] using hx')
    rcases (eventually_atTop_unboundedSubtype_iff hS).mp hbound' with ⟨x₀, hx₀⟩
    refine ⟨Real.toNNReal M, Real.toNNReal_pos.mpr hM, x₀, hx₀⟩
  · rintro ⟨M, hM, x₀, hx₀⟩
    refine ⟨(M : ℝ), by exact_mod_cast hM, ?_⟩
    have hbound' : ∀ᶠ x : S in Filter.atTop, f x ≤ M * g x :=
      (eventually_atTop_unboundedSubtype_iff hS).mpr ⟨x₀, hx₀⟩
    filter_upwards [hbound'] with x hx
    have hx' : ((f x : NNReal) : ℝ) ≤ ((M * g x : NNReal) : ℝ) := by
      exact_mod_cast hx
    simpa [Real.norm_of_nonneg, NNReal.coe_mul] using hx'

/-- Definition 1.15 (2). For functions `f g : (Fin k → NNReal) → NNReal`, the shared-threshold
formulation of `f(x₁, ..., x_k) = O(g(x₁, ..., x_k))` is equivalent to the canonical real-valued
`=O[Filter.atTop]` statement obtained by coercing `f` and `g` to `ℝ`. -/
theorem isBigO_finNNReal_iff
    {k : ℕ} {f g : (Fin k → NNReal) → NNReal} :
    (fun x ↦ (f x : ℝ)) =O[Filter.atTop] (fun x ↦ (g x : ℝ)) ↔
      ∃ M > 0, ∃ x₀ : NNReal, ∀ x : Fin k → NNReal, (∀ i, x₀ < x i) → f x ≤ M * g x := by
  rw [isBigO_iff']
  constructor
  · rintro ⟨M, hM, hbound⟩
    have hbound' : ∀ᶠ x in Filter.atTop, f x ≤ Real.toNNReal M * g x := by
      filter_upwards [hbound] with x hx
      have hx' : (f x : ℝ) ≤ M * (g x : ℝ) := by
        simpa [Real.norm_of_nonneg] using hx
      exact_mod_cast (show (f x : ℝ) ≤ ((Real.toNNReal M * g x : NNReal) : ℝ) by
        simpa [NNReal.coe_mul, Real.coe_toNNReal M hM.le] using hx')
    rw [Filter.eventually_atTop] at hbound'
    rcases hbound' with ⟨x₀, hx₀⟩
    refine ⟨Real.toNNReal M, Real.toNNReal_pos.mpr hM, Finset.univ.sup x₀, ?_⟩
    intro x hx
    apply hx₀ x
    intro i
    exact (Finset.le_sup (Finset.mem_univ i)).trans (le_of_lt (hx i))
  · rintro ⟨M, hM, x₀, hbound⟩
    refine ⟨(M : ℝ), by exact_mod_cast hM, ?_⟩
    have hbound' : ∀ᶠ x in Filter.atTop, f x ≤ M * g x := by
      rw [Filter.eventually_atTop]
      refine ⟨fun _ ↦ x₀ + 1, fun x hx ↦ hbound x (fun i ↦ ?_)⟩
      exact (lt_add_of_pos_right x₀ zero_lt_one).trans_le (hx i)
    filter_upwards [hbound'] with x hx
    have hx' : ((f x : NNReal) : ℝ) ≤ ((M * g x : NNReal) : ℝ) := by
      exact_mod_cast hx
    simpa [Real.norm_of_nonneg, NNReal.coe_mul] using hx'

/-- The source-style positive-threshold formulation is a companion specialization of
`isBigO_finNNReal_iff`; the positivity hypothesis on the threshold is redundant. -/
theorem isBigO_finNNReal_iff_posThreshold
    {k : ℕ} {f g : (Fin k → NNReal) → NNReal} :
    (fun x ↦ (f x : ℝ)) =O[Filter.atTop] (fun x ↦ (g x : ℝ)) ↔
      ∃ M > 0, ∃ x₀ > 0, ∀ x : Fin k → NNReal, (∀ i, x₀ < x i) → f x ≤ M * g x := by
  constructor
  · intro h
    rcases isBigO_finNNReal_iff.mp h with ⟨M, hM, x₀, hbound⟩
    refine ⟨M, hM, max x₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x hx
    exact hbound x (fun i ↦ (le_max_left _ _).trans_lt (hx i))
  · rintro ⟨M, hM, x₀, hx₀, hbound⟩
    exact isBigO_finNNReal_iff.mpr ⟨M, hM, x₀, hbound⟩

end Asymptotics

end
