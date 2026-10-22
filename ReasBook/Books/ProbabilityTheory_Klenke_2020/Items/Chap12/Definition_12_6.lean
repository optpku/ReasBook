/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

variable {E : Type u} [MeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {α : Type*}

private theorem iSup_comap_realFunctional_le [MeasurableSpace α] (P : (α → ℝ) → Prop) :
    (⨆ f : {f : α → ℝ // Measurable f ∧ P f}, MeasurableSpace.comap f.1 inferInstance) ≤
      (inferInstance : MeasurableSpace α) := by
  refine iSup_le fun f ↦ f.2.1.comap_le

/- The sample-sequence map associated with a process `X` is the canonical core function
`Function.swap X`. -/
recall Function.swap

/-- A set of sequences is `n`-symmetric if permuting its first `n` coordinates does not change
membership. -/
def IsNSymmetricSequenceSet (n : ℕ) (s : Set (ℕ → E)) : Prop :=
  ∀ ρ : Equiv.Perm (Fin n), permutePrefix n ρ ⁻¹' s = s

/-- The averaged permutation symmetrization of a real-valued functional on sequence space over the
first `n` coordinates. -/
noncomputable def exchangeableAverage (n : ℕ) (φ : (ℕ → E) → ℝ) : (ℕ → E) → ℝ :=
  fun x ↦ (∑ ρ : Equiv.Perm (Fin n), φ (permutePrefix n ρ x)) / Nat.factorial n

/-- Helper for Definition 12.6: on the first `n` coordinates, `permutePrefix` acts by the chosen
permutation. -/
private theorem permutePrefix_apply_fin {E : Type u} {n : ℕ}
    (ρ : Equiv.Perm (Fin n)) (x : ℕ → E) (i : Fin n) :
    permutePrefix n ρ x i = x (ρ i) := by
  -- On the embedded copy of `Fin n`, the extended permutation is exactly `ρ`.
  simp [permutePrefix, Equiv.Perm.extendDomain_apply_subtype]

/-- Helper for Definition 12.6: composing two prefix permutations multiplies the corresponding
permutations on `Fin n`. -/
private theorem permutePrefix_mul {E : Type u} {n : ℕ}
    (ρ τ : Equiv.Perm (Fin n)) (x : ℕ → E) :
    permutePrefix n ρ (permutePrefix n τ x) = permutePrefix n (τ * ρ) x := by
  funext i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    -- Inside the prefix, both sides are computed by the corresponding product permutation.
    have hleft :
        permutePrefix n ρ (permutePrefix n τ x) i = permutePrefix n τ x (ρ j) := by
      simpa [j] using permutePrefix_apply_fin ρ (permutePrefix n τ x) j
    have hmiddle :
        permutePrefix n τ x (ρ j) = x (τ (ρ j)) := by
      simpa using permutePrefix_apply_fin τ x (ρ j)
    have hright :
        permutePrefix n (τ * ρ) x i = x ((τ * ρ) j) := by
      simpa [j] using permutePrefix_apply_fin (τ * ρ) x j
    rw [hleft, hmiddle, hright]
    simp [Equiv.Perm.mul_apply]
  · -- Outside the moved prefix, every extended permutation fixes the coordinate.
    simp [permutePrefix, Function.comp, hi, Equiv.Perm.extendDomain_apply_not_subtype]

/-- Helper for Definition 12.6: each fiber of the map `ρ ↦ ρ 0` on `Equiv.Perm (Fin n)` has
cardinality `(n - 1)!`. -/
private theorem cardPermApplyZeroFiber (n : ℕ+) (i : Fin (n : ℕ)) :
    Fintype.card {ρ : Equiv.Perm (Fin (n : ℕ)) // ρ 0 = i} = Nat.factorial ((n : ℕ) - 1) := by
  classical
  let c : ℕ := Fintype.card {ρ : Equiv.Perm (Fin (n : ℕ)) // ρ 0 = 0}
  have hconst :
      ∀ j : Fin (n : ℕ), Fintype.card {ρ : Equiv.Perm (Fin (n : ℕ)) // ρ 0 = j} = c := by
    intro j
    -- Every fiber is equivalent to the fiber over `0`.
    dsimp [c]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun ρ ↦ ?_
        invFun := fun ρ ↦ ?_
        left_inv := ?_
        right_inv := ?_ }
    · -- Swapping `j` with `0` sends the `j`-fiber to the `0`-fiber.
      refine ⟨Equiv.swap j 0 * ρ.1, ?_⟩
      simp [Equiv.Perm.mul_apply, ρ.2]
    · -- The same swap is an involution, so it also gives the inverse map.
      refine ⟨Equiv.swap j 0 * ρ.1, ?_⟩
      simp [Equiv.Perm.mul_apply, ρ.2]
    · intro ρ
      ext k
      -- Cancelling the swap on the left recovers the original permutation.
      simp
    · intro ρ
      ext k
      -- The same involutive cancellation proves the right inverse identity.
      simp
  have hcard :
      Nat.factorial (n : ℕ) = (n : ℕ) * c := by
    -- Partition the permutation set by the value of `ρ 0` and replace each fiber by the common
    -- cardinal `c`.
    have hMapsTo :
        ((Finset.univ : Finset (Equiv.Perm (Fin (n : ℕ)))) :
          Set (Equiv.Perm (Fin (n : ℕ)))).MapsTo
          (fun ρ : Equiv.Perm (Fin (n : ℕ)) ↦ ρ 0) (Finset.univ : Finset (Fin (n : ℕ))) :=
      fun _ _ ↦ Finset.mem_univ _
    calc
      Nat.factorial (n : ℕ) =
          ∑ j : Fin (n : ℕ),
            (Finset.filter (fun ρ : Equiv.Perm (Fin (n : ℕ)) ↦ ρ 0 = j)
              (Finset.univ : Finset (Equiv.Perm (Fin (n : ℕ))))).card := by
            simpa [Fintype.card_perm] using
              (Finset.card_eq_sum_card_fiberwise hMapsTo)
      _ = ∑ j : Fin (n : ℕ), Fintype.card {ρ : Equiv.Perm (Fin (n : ℕ)) // ρ 0 = j} := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa using
              (Fintype.card_subtype (fun ρ : Equiv.Perm (Fin (n : ℕ)) ↦ ρ 0 = j)).symm
      _ = ∑ j : Fin (n : ℕ), c := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact hconst j
      _ = (n : ℕ) * c := by
            simp [c]
  have hfiberZero : c = Nat.factorial ((n : ℕ) - 1) := by
    -- Compare the partition count with `n * (n - 1)! = n!`.
    apply Nat.mul_left_cancel n.pos
    calc
      (n : ℕ) * c = Nat.factorial (n : ℕ) := hcard.symm
      _ = (n : ℕ) * Nat.factorial ((n : ℕ) - 1) := by
            exact (Nat.mul_factorial_pred (Nat.ne_of_gt n.pos)).symm
  exact (hconst i).trans hfiberZero

/-- Helper for Definition 12.6: summing `x (ρ 0)` over all finite permutations counts each of the
first `n` coordinates exactly `(n - 1)!` times. -/
private theorem sum_perm_apply_zero_eq_factorialPred_mul_sum (n : ℕ+) (x : ℕ → ℝ) :
    (∑ ρ : Equiv.Perm (Fin (n : ℕ)), x (ρ 0)) =
      (Nat.factorial ((n : ℕ) - 1) : ℝ) * ∑ i : Fin (n : ℕ), x i := by
  classical
  -- Rewrite the sum by grouping permutations according to the value of `ρ 0`.
  have hMapsTo :
      ((Finset.univ : Finset (Equiv.Perm (Fin (n : ℕ)))) :
        Set (Equiv.Perm (Fin (n : ℕ)))).MapsTo
        (fun ρ : Equiv.Perm (Fin (n : ℕ)) ↦ ρ 0) (Finset.univ : Finset (Fin (n : ℕ))) :=
    fun _ _ ↦ Finset.mem_univ _
  calc
    (∑ ρ : Equiv.Perm (Fin (n : ℕ)), x (ρ 0)) =
        ∑ i : Fin (n : ℕ),
          ∑ ρ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (n : ℕ)))) with ρ 0 = i, x i := by
            symm
            exact Finset.sum_fiberwise_of_maps_to' hMapsTo fun i : Fin (n : ℕ) ↦ x i
    _ = ∑ i : Fin (n : ℕ),
          ((Fintype.card {ρ : Equiv.Perm (Fin (n : ℕ)) // ρ 0 = i} : ℝ) * x i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            -- Each inner fiber sum is a constant repeated `#fiber` times.
            have hcard :
                ((Finset.filter (fun ρ : Equiv.Perm (Fin (n : ℕ)) ↦ ρ 0 = i)
                  (Finset.univ : Finset (Equiv.Perm (Fin (n : ℕ))))).card : ℝ) =
                  Fintype.card {ρ : Equiv.Perm (Fin (n : ℕ)) // ρ 0 = i} := by
              exact_mod_cast
                (Fintype.card_subtype (fun ρ : Equiv.Perm (Fin (n : ℕ)) ↦ ρ 0 = i)).symm
            calc
              ∑ ρ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (n : ℕ)))) with ρ 0 = i, x i =
                  ((Finset.filter (fun ρ : Equiv.Perm (Fin (n : ℕ)) ↦ ρ 0 = i)
                    (Finset.univ : Finset (Equiv.Perm (Fin (n : ℕ))))).card : ℝ) * x i := by
                    rw [Finset.sum_const, nsmul_eq_mul]
              _ = (Fintype.card {ρ : Equiv.Perm (Fin (n : ℕ)) // ρ 0 = i} : ℝ) * x i := by
                    rw [hcard]
    _ = ∑ i : Fin (n : ℕ), (Nat.factorial ((n : ℕ) - 1) : ℝ) * x i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [cardPermApplyZeroFiber]
    _ = (Nat.factorial ((n : ℕ) - 1) : ℝ) * ∑ i : Fin (n : ℕ), x i := by
          rw [← Finset.mul_sum]

-- Proof sketch: in the orbit of the first coordinate under the permutation action of `S(n)`,
-- each of the first `n` coordinates appears equally often, so averaging the evaluation map
-- `x ↦ x 0` over all permutations yields the empirical mean of the first `n` coordinates.
/-- The owner permutation average of the first-coordinate functional is the empirical mean of the
first `n` coordinates. -/
theorem exchangeableAverage_apply_zero (n : ℕ+) :
    exchangeableAverage (n : ℕ) (fun x ↦ x 0) =
      fun x ↦ (∑ i : Fin (n : ℕ), x i) / (n : ℝ) := by
  funext x
  have hsum := sum_perm_apply_zero_eq_factorialPred_mul_sum n x
  have hprefix :
      (∑ ρ : Equiv.Perm (Fin (n : ℕ)), permutePrefix (n : ℕ) ρ x 0) =
        ∑ ρ : Equiv.Perm (Fin (n : ℕ)), x (ρ 0) := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    exact permutePrefix_apply_fin ρ x 0
  have hn_ne_zero : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt n.pos)
  have hfactorial_ne_zero : (Nat.factorial ((n : ℕ) - 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ((n : ℕ) - 1)
  have hfactorial :
      (Nat.factorial (n : ℕ) : ℝ) = (n : ℝ) * Nat.factorial ((n : ℕ) - 1) := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt n.pos)).symm
  -- Substitute the fiberwise count and cancel the common factorial factor.
  calc
    exchangeableAverage (n : ℕ) (fun y ↦ y 0) x =
        ((Nat.factorial ((n : ℕ) - 1) : ℝ) * ∑ i : Fin (n : ℕ), x i) /
          Nat.factorial (n : ℕ) := by
            rw [exchangeableAverage, hprefix, hsum]
    _ = ((Nat.factorial ((n : ℕ) - 1) : ℝ) * ∑ i : Fin (n : ℕ), x i) /
          ((n : ℝ) * Nat.factorial ((n : ℕ) - 1)) := by
            rw [hfactorial]
    _ = (∑ i : Fin (n : ℕ), x i) / (n : ℝ) := by
          field_simp [hn_ne_zero, hfactorial_ne_zero]

-- Proof sketch: composing the permutation average with another permutation of the first `n`
-- coordinates just reindexes the finite sum over `Equiv.Perm (Fin n)`.
/-- The owner permutation average `exchangeableAverage n φ` is `n`-symmetric. -/
theorem exchangeableAverage_isNSymmetric {E : Type u} (n : ℕ) (φ : (ℕ → E) → ℝ) :
    IsNSymmetricSequenceMap n (exchangeableAverage n φ) := by
  intro ρ x
  -- Rewrite the inner permutation composition as multiplication in `Equiv.Perm (Fin n)`.
  have hsumRewrite :
      ∀ τ : Equiv.Perm (Fin n),
        φ (permutePrefix n τ (permutePrefix n ρ x)) =
          φ (permutePrefix n (ρ * τ) x) := by
    intro τ
    simpa using congrArg φ (permutePrefix_mul τ ρ x)
  have hsumPrefix :
      (∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ (permutePrefix n ρ x)) : ℝ) =
        ∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n (ρ * τ) x) := by
    let F : Equiv.Perm (Fin n) → ℝ := fun τ ↦ φ (permutePrefix n τ (permutePrefix n ρ x))
    let G : Equiv.Perm (Fin n) → ℝ := fun τ ↦ φ (permutePrefix n (ρ * τ) x)
    have hFG : F = G := by
      funext τ
      exact hsumRewrite τ
    simpa [F, G] using congrArg (fun H : Equiv.Perm (Fin n) → ℝ ↦ ∑ τ, H τ) hFG
  have hsumReindex :
      (∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ (permutePrefix n ρ x)) : ℝ) =
        ∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ x) := by
    calc
      (∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ (permutePrefix n ρ x)) : ℝ) =
          ∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n (ρ * τ) x) := hsumPrefix
      _ = ∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ x) := by
            -- Reindex the finite sum by left multiplication with `ρ`.
            simpa using
              (Function.Bijective.sum_comp (Group.mulLeft_bijective ρ)
                (fun τ : Equiv.Perm (Fin n) ↦ φ (permutePrefix n τ x)))
  simp [exchangeableAverage, hsumReindex]

/-- The sigma-algebra on sequence space generated by measurable `n`-symmetric real-valued
functionals. -/
abbrev nSymmetricSequenceSigmaAlgebra (n : ℕ) : MeasurableSpace (ℕ → E) :=
  ⨆ f : {f : (ℕ → E) → ℝ // Measurable f ∧ IsNSymmetricSequenceMap n f},
    MeasurableSpace.comap f.1 inferInstance

/-- The sigma-algebra on sequence space generated by measurable symmetric real-valued
functionals. -/
abbrev exchangeableSequenceSigmaAlgebra : MeasurableSpace (ℕ → E) :=
  ⨆ f : {f : (ℕ → E) → ℝ // Measurable f ∧ IsSymmetricSequenceMap f},
    MeasurableSpace.comap f.1 inferInstance

/-- The pullback to `Ω` of the `n`-symmetric sigma-algebra along a sequence-valued map `X`. -/
abbrev nExchangeableSigmaAlgebra (X : Ω → ℕ → E) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap X (nSymmetricSequenceSigmaAlgebra n)

/-- The `n`-symmetric sigma-algebra on sequence space is a sub-`σ`-algebra of the ambient product
measurable space. -/
theorem nSymmetricSequenceSigmaAlgebra_le (n : ℕ) :
    nSymmetricSequenceSigmaAlgebra n ≤
      (inferInstance : MeasurableSpace (ℕ → E)) := by
  exact iSup_comap_realFunctional_le (IsNSymmetricSequenceMap n)

/-- Helper for Definition 12.6: the preimage of a set under an `n`-symmetric map is
`n`-symmetric. -/
private theorem isNSymmetricSequenceSet_preimage {E : Type u} {n : ℕ} {f : (ℕ → E) → ℝ}
    (hf : IsNSymmetricSequenceMap n f) (t : Set ℝ) :
    IsNSymmetricSequenceSet n (f ⁻¹' t) := by
  intro ρ
  ext x
  -- Membership is preserved because `f` is invariant under the prefix permutation.
  simp [hf ρ x]

/-- Helper for Definition 12.6: the indicator of an `n`-symmetric set is an `n`-symmetric
real-valued map. -/
private theorem indicatorConst_isNSymmetricSequenceMap {E : Type u} {n : ℕ}
    {s : Set (ℕ → E)}
    (hsym : IsNSymmetricSequenceSet n s) :
    IsNSymmetricSequenceMap n (s.indicator (fun _ ↦ (1 : ℝ))) := by
  intro ρ x
  -- The set-level invariance transfers directly to the indicator values.
  have hmem : permutePrefix n ρ x ∈ s ↔ x ∈ s := by
    simpa using (Set.ext_iff.mp (hsym ρ) x)
  by_cases hx : x ∈ s
  · have hperm : permutePrefix n ρ x ∈ s := hmem.mpr hx
    simp [Set.indicator, hx, hperm]
  · have hperm : permutePrefix n ρ x ∉ s := by
      exact fun hx' ↦ hx (hmem.mp hx')
    simp [Set.indicator, hx, hperm]

/-- A set of sequences is measurable for the `n`-symmetric sigma-algebra exactly when it is
ambient measurable and invariant under permutations of its first `n` coordinates. -/
theorem measurableSet_nSymmetricSequenceSigmaAlgebra_iff
    (n : ℕ) (s : Set (ℕ → E)) :
    MeasurableSet[nSymmetricSequenceSigmaAlgebra n] s ↔
      MeasurableSet s ∧ IsNSymmetricSequenceSet n s := by
  constructor
  · intro hs
    rw [MeasurableSpace.measurableSet_iSup] at hs
    -- Propagate ambient measurability and prefix invariance through the generated `σ`-algebra.
    refine MeasurableSpace.generateFrom_induction
      {t : Set (ℕ → E) |
        ∃ f : {f : (ℕ → E) → ℝ // Measurable f ∧ IsNSymmetricSequenceMap n f},
          MeasurableSet[MeasurableSpace.comap f.1 inferInstance] t}
      (fun t _ ↦ MeasurableSet t ∧ IsNSymmetricSequenceSet n t) ?_ ?_ ?_ ?_ s hs
    · intro t ht _
      rcases ht with ⟨f, ht⟩
      rcases (MeasurableSpace.measurableSet_comap.mp ht) with ⟨u, hu, rfl⟩
      exact ⟨measurableSet_preimage f.2.1 hu, isNSymmetricSequenceSet_preimage f.2.2 u⟩
    · exact ⟨MeasurableSet.empty, by intro ρ; rfl⟩
    · intro t ht hprop
      rcases hprop with ⟨ht_meas, ht_symm⟩
      refine ⟨ht_meas.compl, ?_⟩
      intro ρ
      ext x
      -- Complements preserve the same invariance equation pointwise.
      have hmem : permutePrefix n ρ x ∈ t ↔ x ∈ t := by
        exact Set.ext_iff.mp (ht_symm ρ) x
      simp [Set.mem_preimage, hmem]
    · intro t ht hprop
      refine ⟨MeasurableSet.iUnion fun m ↦ (hprop m).1, ?_⟩
      intro ρ
      ext x
      -- Countable unions preserve invariance because each stage is invariant.
      simp only [Set.mem_preimage, Set.mem_iUnion]
      constructor
      · rintro ⟨(k : ℕ), hk⟩
        exact ⟨k, (Set.ext_iff.mp ((hprop k).2 ρ) x).mp hk⟩
      · rintro ⟨(k : ℕ), hk⟩
        exact ⟨k, (Set.ext_iff.mp ((hprop k).2 ρ) x).mpr hk⟩
  · rintro ⟨hs, hsym⟩
    let f : {f : (ℕ → E) → ℝ // Measurable f ∧ IsNSymmetricSequenceMap n f} :=
      ⟨s.indicator (fun _ ↦ (1 : ℝ)),
        (measurable_indicator_const_iff (1 : ℝ)).2 hs,
        indicatorConst_isNSymmetricSequenceMap hsym⟩
    -- The set is the preimage of `{1}` under its invariant indicator.
    have hs_comap :
        MeasurableSet[MeasurableSpace.comap f.1 (inferInstance : MeasurableSpace ℝ)] s := by
      rw [MeasurableSpace.measurableSet_comap]
      refine ⟨{1}, measurableSet_singleton 1, ?_⟩
      ext x
      by_cases hx : x ∈ s
      · simp [f, hx]
      · simp [f, hx]
    exact
      (show MeasurableSpace.comap f.1 (inferInstance : MeasurableSpace ℝ) ≤
          nSymmetricSequenceSigmaAlgebra n from
        le_iSup_of_le f le_rfl) s hs_comap

/-- The exchangeable sigma-algebra of a sequence-valued map `X` from Definition 12.6 is the
pullback of the sigma-algebra on `E^N` generated by measurable symmetric real-valued
functionals. -/
abbrev exchangeableSigmaAlgebra (X : Ω → ℕ → E) : MeasurableSpace Ω :=
  MeasurableSpace.comap X exchangeableSequenceSigmaAlgebra

/-- The symmetric sigma-algebra on sequence space is a sub-`σ`-algebra of the ambient product
measurable space. -/
theorem exchangeableSequenceSigmaAlgebra_le :
    exchangeableSequenceSigmaAlgebra ≤
      (inferInstance : MeasurableSpace (ℕ → E)) := by
  exact iSup_comap_realFunctional_le IsSymmetricSequenceMap

/-- Every finite-permutation-invariant stage of a measurable sequence-valued map is a
sub-`σ`-algebra of the ambient measurable space. -/
theorem nExchangeableSigmaAlgebra_le {X : Ω → ℕ → E} (hX : Measurable X) (n : ℕ) :
    nExchangeableSigmaAlgebra X n ≤ (inferInstance : MeasurableSpace Ω) := by
  refine (MeasurableSpace.comap_mono (nSymmetricSequenceSigmaAlgebra_le n)).trans ?_
  exact hX.comap_le

-- Proof sketch: `exchangeableSigmaAlgebra X` is the pullback measurable space generated by
-- symmetric sequence functionals, viewed canonically as a sub-`σ`-algebra of the ambient
-- measurable space on `Ω`.
/-- The exchangeable `σ`-algebra generated by a measurable sequence-valued map is a
sub-`σ`-algebra of the ambient measurable space. -/
theorem exchangeableSigmaAlgebra_le {X : Ω → ℕ → E} (hX : Measurable X) :
    exchangeableSigmaAlgebra X ≤ (inferInstance : MeasurableSpace Ω) := by
  refine (MeasurableSpace.comap_mono exchangeableSequenceSigmaAlgebra_le).trans ?_
  exact hX.comap_le

-- Proof sketch: identify a symmetric sequence functional with a functional that is `n`-symmetric
-- for every `n`, then compare the sigma-algebra generated by all such functionals with the infimum
-- of the `n`-symmetric generated sigma-algebras.
/-- The symmetric sigma-algebra on sequence space is the intersection of the `n`-symmetric
sigma-algebras. -/
theorem exchangeableSequenceSigmaAlgebra_eq_iInf_nSymmetricSequenceSigmaAlgebra :
    (exchangeableSequenceSigmaAlgebra : MeasurableSpace (ℕ → E)) =
      ⨅ n, nSymmetricSequenceSigmaAlgebra n := by
  ext s
  rw [MeasurableSpace.measurableSet_iInf]
  constructor
  · intro hs n
    -- A symmetric generator is `n`-symmetric for every `n`, so the exchangeable stage sits
    -- inside each finite stage.
    have hle : (exchangeableSequenceSigmaAlgebra : MeasurableSpace (ℕ → E)) ≤
        nSymmetricSequenceSigmaAlgebra n := by
      refine iSup_le fun f ↦ ?_
      exact le_iSup_of_le ⟨f.1, f.2.1, f.2.2 n⟩ le_rfl
    exact hle s hs
  · intro hs
    have hs_meas : MeasurableSet s :=
      ((measurableSet_nSymmetricSequenceSigmaAlgebra_iff 0 s).1 (hs 0)).1
    have hs_symm : ∀ n, IsNSymmetricSequenceSet n s := fun n ↦
      ((measurableSet_nSymmetricSequenceSigmaAlgebra_iff n s).1 (hs n)).2
    let f : {f : (ℕ → E) → ℝ // Measurable f ∧ IsSymmetricSequenceMap f} :=
      ⟨s.indicator (fun _ ↦ (1 : ℝ)),
        (measurable_indicator_const_iff (1 : ℝ)).2 hs_meas,
        fun n ↦ indicatorConst_isNSymmetricSequenceMap (hs_symm n)⟩
    -- The common indicator witness is measurable in the symmetric generator `σ`-algebra.
    have hs_comap :
        MeasurableSet[MeasurableSpace.comap f.1 (inferInstance : MeasurableSpace ℝ)] s := by
      rw [MeasurableSpace.measurableSet_comap]
      refine ⟨{1}, measurableSet_singleton 1, ?_⟩
      ext x
      by_cases hx : x ∈ s
      · simp [f, hx]
      · simp [f, hx]
    exact
      (show MeasurableSpace.comap f.1 (inferInstance : MeasurableSpace ℝ) ≤
          exchangeableSequenceSigmaAlgebra from
        le_iSup_of_le f le_rfl) s hs_comap

/-- Helper for Definition 12.6: pulling back the symmetric sequence sigma-algebra along `X`
always lands inside every finite exchangeable stage. -/
theorem exchangeableSigmaAlgebra_le_iInf_nExchangeableSigmaAlgebra
    {Ω : Type v} (X : Ω → ℕ → E) :
    (exchangeableSigmaAlgebra X : MeasurableSpace Ω) ≤ ⨅ n, nExchangeableSigmaAlgebra X n := by
  -- Pull back the sequence-space `iInf` description and use monotonicity of `comap`.
  rw [exchangeableSigmaAlgebra,
    exchangeableSequenceSigmaAlgebra_eq_iInf_nSymmetricSequenceSigmaAlgebra]
  exact le_iInf fun n ↦ MeasurableSpace.comap_mono (iInf_le _ n)

-- Source-faithful repair: Definition 12.6 identifies the process-level exchangeable
-- `σ`-algebra with the pullback of the sequence-space exchangeable `σ`-algebra, and the latter is
-- the intersection of the finite symmetric sequence `σ`-algebras.
/-- Definition 12.6: the exchangeable sigma-algebra of `X` is the pullback along `X` of the
intersection of the finite symmetric sigma-algebras on sequence space. -/
theorem exchangeableSigmaAlgebra_eq_comap_iInf_nSymmetricSequenceSigmaAlgebra
    {Ω : Type v} (X : Ω → ℕ → E) :
    (exchangeableSigmaAlgebra X : MeasurableSpace Ω) =
      MeasurableSpace.comap X (⨅ n, nSymmetricSequenceSigmaAlgebra n) := by
  -- Transport the sequence-space identity through the pullback measurable space `comap X`.
  simpa [exchangeableSigmaAlgebra] using
    congrArg (fun M : MeasurableSpace (ℕ → E) ↦ MeasurableSpace.comap X M)
      exchangeableSequenceSigmaAlgebra_eq_iInf_nSymmetricSequenceSigmaAlgebra
