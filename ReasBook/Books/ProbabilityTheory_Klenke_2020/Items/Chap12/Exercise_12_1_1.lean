/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

section

variable {E : Type u} [MeasurableSpace E]
variable {n : ℕ+}

/-- Helper for Exercise 12.1.1: reindexing a tuple by a permutation does not change its empirical
distribution. -/
lemma empiricalDistributionTuple_comp_perm (ρ : Equiv.Perm (Fin n)) (x : Fin n → E) :
    empiricalDistributionTuple (x ∘ ρ) = empiricalDistributionTuple x := by
  -- Compare the two probability measures on arbitrary measurable sets.
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  rw [empiricalDistributionTuple, empiricalDistributionTuple]
  rw [empiricalDistribution_toMeasure, empiricalDistribution_toMeasure]
  simp only [Measure.smul_apply, hs, Function.comp_apply, Measure.finset_sum_apply,
    Measure.dirac_apply']
  congr 1
  exact Fintype.sum_bijective ρ ρ.bijective _ _ (fun i ↦ rfl)

/-- Helper for Exercise 12.1.1: if two finite tuples have the same fiber cardinalities at every
value, then they differ by a coordinate permutation. -/
lemma exists_perm_of_fiberCard_eq {α : Type*} {m : ℕ} {x y : Fin m → α}
    (hcard : ∀ a : α, Nat.card {i // x i = a} = Nat.card {i // y i = a}) :
    ∃ ρ : Equiv.Perm (Fin m), y = x ∘ ρ := by
  classical
  let e : ∀ a : α, {i // y i = a} ≃ {i // x i = a} := fun a ↦
    by
      exact Classical.choice (Finite.card_eq.mp (hcard a).symm)
  let σFun : Fin m → Fin m := fun i ↦ (e (y i) ⟨i, rfl⟩).1
  let σInv : Fin m → Fin m := fun i ↦ ((e (x i)).symm ⟨i, rfl⟩).1
  have hσFun_eq :
      ∀ {i : Fin m} {a : α} (h : y i = a), σFun i = (e a ⟨i, h⟩).1 := by
    intro i a h
    subst h
    rfl
  have hσInv_eq :
      ∀ {i : Fin m} {a : α} (h : x i = a), σInv i = ((e a).symm ⟨i, h⟩).1 := by
    intro i a h
    subst h
    rfl
  have hLeft : Function.LeftInverse σInv σFun := by
    intro i
    -- Proof comment: `σFun` moves `i` to the matching coordinate in the `x`-fiber of `y i`, and
    -- `σInv` returns along the inverse fiber equivalence.
    rw [hσInv_eq ((e (y i) ⟨i, rfl⟩).2)]
    simpa using congrArg Subtype.val ((e (y i)).left_inv ⟨i, rfl⟩)
  have hRight : Function.RightInverse σInv σFun := by
    intro i
    -- Proof comment: the same fiberwise inverse argument proves the reverse composition is the
    -- identity as well.
    rw [hσFun_eq (((e (x i)).symm ⟨i, rfl⟩).2)]
    simpa using congrArg Subtype.val (((e (x i)).symm).left_inv ⟨i, rfl⟩)
  let ρ : Equiv.Perm (Fin m) := ⟨σFun, σInv, hLeft, hRight⟩
  refine ⟨ρ, ?_⟩
  funext i
  -- Proof comment: by construction, `ρ i` lies in the `x`-fiber carrying the same value as
  -- the `i`th coordinate of `y`.
  simpa [ρ, σFun, Function.comp_apply] using ((e (y i) ⟨i, rfl⟩).2).symm

/-- Helper for Exercise 12.1.1: equality of empirical distributions should force equality of the
underlying tuple multisets, hence equality up to a coordinate permutation. -/
lemma exists_perm_of_empiricalDistributionTuple_eq
    [MeasurableSpace.SeparatesPoints E] {x y : Fin n → E}
    (hxy : empiricalDistributionTuple x = empiricalDistributionTuple y) :
    ∃ ρ : Equiv.Perm (Fin n), y = x ∘ ρ := by
  classical
  -- Route correction: instead of transporting `List.ofFn` permutations through brittle `Fin`
  -- casts, compare empirical masses on singleton fibers of the finite joint range.
  let s : Set E := Set.range x ∪ Set.range y
  have hsFinite : s.Finite := (Set.finite_range x).union (Set.finite_range y)
  letI : Finite s := hsFinite.to_subtype
  letI : Fintype s := Fintype.ofFinite s
  letI : Countable s := hsFinite.countable
  letI : MeasurableSingletonClass s := inferInstance
  let xs : Fin n → s := fun i ↦ ⟨x i, Or.inl ⟨i, rfl⟩⟩
  let ys : Fin n → s := fun i ↦ ⟨y i, Or.inr ⟨i, rfl⟩⟩
  have hmass_of_lift :
      ∀ {w : Fin n → E} (ws : Fin n → s), (∀ i, (ws i : E) = w i) →
        ∀ {z : s} {t : Set E}, MeasurableSet t → Subtype.val ⁻¹' t = ({z} : Set s) →
          (((empiricalDistributionTuple w : ProbabilityMeasure E) : Measure E) t) =
            (n : ENNReal)⁻¹ * Fintype.card {i // ws i = z} := by
    intro w ws hws z t ht hpre
    have hmem : ∀ i, w i ∈ t ↔ ws i = z := by
      intro i
      have hpre' : ws i ∈ Subtype.val ⁻¹' t ↔ ws i = z := by
        simp [hpre]
      change w i ∈ t ↔ ws i = z
      simpa [Set.mem_preimage, hws i] using hpre'
    -- Proof comment: expanding the empirical distribution turns the mass of `t` into the
    -- normalized number of coordinates whose lifted value equals `z`.
    rw [empiricalDistributionTuple, empiricalDistribution_toMeasure]
    rw [Measure.smul_apply, Measure.finset_sum_apply]
    simp only [ht, smul_eq_mul, Measure.dirac_apply', Finset.sum_indicator_eq_sum_filter]
    have hsum :
        ∑ i : Fin n, Set.indicator t (fun _ ↦ (1 : ENNReal)) (w i) =
          (Fintype.card {i // ws i = z} : ENNReal) := by
      have hcardEq : Fintype.card {i // w i ∈ t} = Fintype.card {i // ws i = z} :=
        Fintype.card_congr
          { toFun := fun i ↦ ⟨i.1, (hmem i.1).mp i.2⟩
            invFun := fun i ↦ ⟨i.1, (hmem i.1).mpr i.2⟩
            left_inv := by
              intro i
              cases i
              rfl
            right_inv := by
              intro i
              cases i
              rfl }
      simpa [Set.indicator, hmem, Fintype.card_subtype] using
        congrArg (fun k : ℕ ↦ (k : ENNReal)) hcardEq
    simpa [Finset.sum_indicator_eq_sum_filter] using
      congrArg (fun r : ENNReal ↦ (n : ENNReal)⁻¹ * r) hsum
  -- Proof comment: once the coordinate fibers in the finite joint range have the same sizes, the
  -- tuples differ only by a permutation of `Fin n`.
  rcases exists_perm_of_fiberCard_eq (α := s) (m := n) (x := xs) (y := ys)
      (fun z ↦ by
        rcases (MeasurableSet.singleton z : MeasurableSet ({z} : Set s)) with ⟨t, ht, hpre⟩
        have hmass :
            (((empiricalDistributionTuple x : ProbabilityMeasure E) : Measure E) t) =
              (((empiricalDistributionTuple y : ProbabilityMeasure E) : Measure E) t) := by
          exact congrArg (fun μ : ProbabilityMeasure E => (μ : Measure E) t) hxy
        have hmassX :
            (((empiricalDistributionTuple x : ProbabilityMeasure E) : Measure E) t) =
              (n : ENNReal)⁻¹ * Fintype.card {i // xs i = z} :=
          hmass_of_lift xs (fun _ ↦ rfl) ht hpre
        have hmassY :
            (((empiricalDistributionTuple y : ProbabilityMeasure E) : Measure E) t) =
              (n : ENNReal)⁻¹ * Fintype.card {i // ys i = z} :=
          hmass_of_lift ys (fun _ ↦ rfl) ht hpre
        have hn : (n : ENNReal) ≠ 0 := by
          exact_mod_cast n.ne_zero
        have hfactor0 : ((n : ENNReal)⁻¹) ≠ 0 := by
          simp
        have hcardENN :
            (Fintype.card {i // xs i = z} : ENNReal) = Fintype.card {i // ys i = z} := by
          apply (ENNReal.mul_right_inj hfactor0 (by simp)).mp
          simpa [hmassX, hmassY] using hmass
        have hcardNat : Nat.card {i // xs i = z} = Nat.card {i // ys i = z} := by
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          exact_mod_cast hcardENN
        exact hcardNat) with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  funext i
  simpa [xs, ys, Function.comp_apply] using congrArg Subtype.val (congrFun hρ i)

/- Source/core/bridge triage: this file stays `source-facing`. It concerns symmetric functionals on
the finite tuple space `Fin n → E`. The sequence-space owner `nExchangeableSigmaAlgebra` from
Definition 12.6 is a different layer because it also retains the tail coordinates. -/

-- Proof sketch: a symmetric map on `Eⁿ` depends only on the unordered collection of its input
-- values. Under the point-separating hypothesis on the measurable space of `E`, this unordered
-- collection is equivalently encoded by the empirical distribution `n⁻¹ ∑ i, δ_{x i}`.
/-- Exercise 12.1.1: every symmetric map on `Eⁿ` factors through the empirical distribution of the
tuple. This is the source-facing finite-tuple empirical-measure formulation; the symmetric power
`Sym E n` is only an internal quotient model of the same information. -/
theorem symmetric_function_factors_through_empiricalDistribution
    [MeasurableSpace.SeparatesPoints E]
    (f : (Fin n → E) → ℝ) (hf : IsSymmetricMap f) :
    ∃ g : ProbabilityMeasure E → ℝ,
      f = fun x ↦ g (empiricalDistributionTuple (fun i ↦ x i)) := by
  classical
  let g : ProbabilityMeasure E → ℝ := fun μ =>
    if hμ : ∃ x : Fin n → E, empiricalDistributionTuple x = μ then
      f (Classical.choose hμ)
    else 0
  refine ⟨g, ?_⟩
  funext x
  -- Choose a representative of the empirical-distribution fiber through `x`.
  have hx : ∃ y : Fin n → E, empiricalDistributionTuple y = empiricalDistributionTuple x := ⟨x, rfl⟩
  simp only [g, dif_pos hx]
  rcases exists_perm_of_empiricalDistributionTuple_eq
      (x := Classical.choose hx) (y := x) (Classical.choose_spec hx) with ⟨ρ, hρ⟩
  -- Symmetry identifies all tuples in the same empirical-distribution fiber.
  calc
    f x = f (Classical.choose hx ∘ ρ) := congrArg f hρ
    _ = f (Classical.choose hx) := hf ρ (Classical.choose hx)

end
