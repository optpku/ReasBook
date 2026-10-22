/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Restrict a two-sided path to its nonnegative coordinates. -/
def nonnegativePathRestriction : (ℤ → E) → ℕ → E :=
  fun ω n ↦ ω n

/-- Helper for Lemma 20.4: stationarity at shift `0` supplies the a.e. measurable one-sided path
map of the original process. -/
private theorem aemeasurableProcessMap
    (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω) (hX : IsStationaryProcess X P) :
    AEMeasurable (fun ω n ↦ X n ω) (P : Measure Ω) := by
  -- Proof comment: the shift-`0` law comparison is the original process law on both sides.
  simpa using (hX.identDistrib 0).aemeasurable_snd

/-- Helper for Lemma 20.4: a finite set of integer coordinates is padded into `ℕ` by the sum of
their absolute values. -/
private def leftPadding (J : Finset ℤ) : ℕ :=
  Finset.sum J Int.natAbs

/-- Helper for Lemma 20.4: the padding is monotone under inclusion of finite index sets. -/
private theorem leftPadding_mono {J I : Finset ℤ} (hJI : J ⊆ I) :
    leftPadding J ≤ leftPadding I := by
  -- Proof comment: enlarging the finite index set only adds nonnegative `natAbs` terms.
  classical
  simpa [leftPadding] using
    Finset.sum_le_sum_of_subset_of_nonneg hJI (fun j _ _ => Nat.zero_le (Int.natAbs j))

/-- Helper for Lemma 20.4: every coordinate of `J` becomes nonnegative after shifting by
`leftPadding J`. -/
private theorem nonneg_add_leftPadding (J : Finset ℤ) {j : ℤ} (hj : j ∈ J) :
    0 ≤ (j : ℤ) + leftPadding J := by
  -- Proof comment: `leftPadding J` dominates `natAbs j`, hence also the left tail `-j`.
  have hle : Int.natAbs j ≤ leftPadding J := by
    classical
    simpa [leftPadding] using
      (Finset.single_le_sum (fun i _ => Nat.zero_le (Int.natAbs i)) hj)
  have hle' : ((Int.natAbs j : ℕ) : ℤ) ≤ leftPadding J := by
    exact_mod_cast hle
  cases le_or_gt 0 j with
  | inl hj0 =>
      rw [Int.natAbs_of_nonneg hj0] at hle'
      omega
  | inr hj0 =>
      have hjle0 : j ≤ 0 := le_of_lt hj0
      rw [Int.ofNat_natAbs_of_nonpos hjle0] at hle'
      omega

/-- Helper for Lemma 20.4: read the coordinates in `J` from a one-sided path after shifting by
`N`. -/
private def paddedPathRestriction (J : Finset ℤ) (N : ℕ) : (ℕ → E) → J → E :=
  fun x j ↦ x (Int.toNat ((j : ℤ) + N))

/-- Helper for Lemma 20.4: the padded finite-coordinate map is measurable. -/
private theorem measurable_paddedPathRestriction (J : Finset ℤ) (N : ℕ) :
    Measurable (paddedPathRestriction (E := E) J N) := by
  -- Proof comment: each output coordinate is evaluation of the input path at a fixed natural time.
  refine measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_pi_apply (Int.toNat ((j : ℤ) + N))

/-- Helper for Lemma 20.4: the finite-dimensional law obtained from the shifted one-sided
coordinates. -/
private noncomputable def paddedFiniteLaw (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω)
    (J : Finset ℤ) (N : ℕ) : Measure (J → E) :=
  (P : Measure Ω).map
    (paddedPathRestriction (E := E) J N ∘ fun ω n ↦ X n ω)

/-- Helper for Lemma 20.4: increasing the padding does not change the finite-dimensional law. -/
private theorem paddedFiniteLaw_eq_of_le
    (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω) (hX : IsStationaryProcess X P)
    (J : Finset ℤ) {N M : ℕ} (hNM : N ≤ M)
    (hN : ∀ j : J, 0 ≤ (j : ℤ) + N) :
    paddedFiniteLaw X P J N = paddedFiniteLaw X P J M := by
  let k : ℕ := M - N
  have hk : M = N + k := by
    -- Proof comment: the larger padding is the smaller padding plus a natural shift.
    dsimp [k]
    exact (Nat.add_sub_of_le hNM).symm
  have hshift :
      IdentDistrib
        (paddedPathRestriction (E := E) J N ∘ fun ω n ↦ X (k + n) ω)
        (paddedPathRestriction (E := E) J N ∘ fun ω n ↦ X n ω)
        (P : Measure Ω) (P : Measure Ω) :=
    (hX.identDistrib k).comp (measurable_paddedPathRestriction (E := E) J N)
  calc
    paddedFiniteLaw X P J N
        = Measure.map
            (paddedPathRestriction (E := E) J N ∘ fun ω n ↦ X (k + n) ω)
            (P : Measure Ω) := by
          -- Proof comment: stationarity identifies the padded restriction at padding `N`
          -- with the same restriction applied after shifting the one-sided process by `k`.
          simpa [paddedFiniteLaw] using hshift.map_eq.symm
    _ = paddedFiniteLaw X P J M := by
          -- Proof comment: after rewriting `M = N + k`, the shifted coordinates match
          -- exactly the padded restriction at the larger padding `M`.
          rw [paddedFiniteLaw]
          apply Measure.map_congr
          filter_upwards [] with ω
          ext j
          dsimp [paddedPathRestriction]
          have hjN : 0 ≤ (j : ℤ) + N := hN j
          have hjM : 0 ≤ (j : ℤ) + M := by
            rw [hk]
            omega
          have hindex :
              k + Int.toNat ((j : ℤ) + N) = Int.toNat ((j : ℤ) + M) := by
            have hindex' :
                ((k + Int.toNat ((j : ℤ) + N) : ℕ) : ℤ) = Int.toNat ((j : ℤ) + M) := by
              rw [Int.natCast_add, Int.toNat_of_nonneg hjN, Int.toNat_of_nonneg hjM, hk]
              omega
            exact_mod_cast hindex'
          rw [hindex]

/-- Helper for Lemma 20.4: the canonical finite-dimensional law on a finite subset of `ℤ`. -/
private noncomputable def twoSidedFiniteLaw (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω)
    (J : Finset ℤ) : Measure (J → E) :=
  paddedFiniteLaw X P J (leftPadding J)

/-- Helper for Lemma 20.4: the canonical finite-dimensional laws on `Finset ℤ` form a projective
family. -/
private theorem isProjectiveMeasureFamily_twoSidedFiniteLaw
    (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω) (hX : IsStationaryProcess X P) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ ↦ E) (twoSidedFiniteLaw X P) := by
  intro I J hJI
  let N : ℕ := leftPadding I
  have hAe :
      ∀ j : ℤ, AEMeasurable (fun ω ↦ X (Int.toNat ((j : ℤ) + N)) ω) (P : Measure Ω) := by
    -- Proof comment: each shifted coordinate is an evaluation of the a.e. measurable path map.
    have hPath : AEMeasurable (fun ω n ↦ X n ω) (P : Measure Ω) :=
      aemeasurableProcessMap X P hX
    intro j
    exact (measurable_pi_apply (Int.toNat ((j : ℤ) + N))).aemeasurable.comp_aemeasurable hPath
  have hprojN :=
    ProbabilityTheory.isProjectiveMeasureFamily_map_restrict
      (P := (P : Measure Ω))
      (𝓧 := fun _ : ℤ ↦ E)
      (X := fun j ω ↦ X (Int.toNat ((j : ℤ) + N)) ω)
      hAe
  have hnormalizeJ :
      twoSidedFiniteLaw X P J = paddedFiniteLaw X P J N := by
    -- Proof comment: once the padding reaches `leftPadding I`, the `J`-law can be normalized
    -- from its own left padding to the larger common padding.
    unfold twoSidedFiniteLaw
    exact paddedFiniteLaw_eq_of_le X P hX J (leftPadding_mono hJI)
      (fun j ↦ nonneg_add_leftPadding J j.2)
  have hprojN' :
      paddedFiniteLaw X P J N =
        (paddedFiniteLaw X P I N).map (Finset.restrict₂ (π := fun _ : ℤ ↦ E) hJI) := by
    -- Proof comment: fixed-padding finite-dimensional laws are projective by the owner-level
    -- `map_restrict` theorem, specialized to the constant family `fun _ : ℤ ↦ E`.
    simpa [paddedFiniteLaw, paddedPathRestriction, Function.comp_def, N] using hprojN I J hJI
  calc
    twoSidedFiniteLaw X P J
        = paddedFiniteLaw X P J N := hnormalizeJ
    _ = (paddedFiniteLaw X P I N).map (Finset.restrict₂ (π := fun _ : ℤ ↦ E) hJI) := hprojN'
    _ = (twoSidedFiniteLaw X P I).map (Finset.restrict₂ (π := fun _ : ℤ ↦ E) hJI) := by
          rfl

/-- Helper for Lemma 20.4: an embedded nonnegative index belongs to the corresponding embedded
finite subset of `ℤ`. -/
private theorem mem_embeddedNat (I : Finset ℕ) {n : ℕ} (hn : n ∈ I) :
    (n : ℤ) ∈ I.map (Nat.castEmbedding (R := ℤ)) := by
  exact Finset.mem_map.mpr ⟨n, hn, rfl⟩

/-- Helper for Lemma 20.4: restrict a tuple on the embedded finite subset of `ℤ` back to the
original finite subset of `ℕ`. -/
private def restrictFromEmbeddedNat (I : Finset ℕ) :
    (I.map (Nat.castEmbedding (R := ℤ)) → E) → I → E :=
  fun x i ↦ x ⟨(i : ℤ), mem_embeddedNat I i.2⟩

/-- Helper for Lemma 20.4: the restriction map from embedded integer indices back to natural
indices is measurable. -/
private theorem measurable_restrictFromEmbeddedNat (I : Finset ℕ) :
    Measurable (restrictFromEmbeddedNat (E := E) I) := by
  -- Proof comment: each coordinate is evaluation at the corresponding embedded natural index.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (⟨(i : ℤ), mem_embeddedNat I i.2⟩ :
    I.map (Nat.castEmbedding (R := ℤ)))

/-- Helper for Lemma 20.4: on embedded finite subsets of `ℕ`, the two-sided finite laws recover
the original one-sided finite-dimensional distributions. -/
private theorem embeddedNatFiniteLaw_eq_original
    (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω) (hX : IsStationaryProcess X P)
    (I : Finset ℕ) :
    Measure.map (restrictFromEmbeddedNat (E := E) I)
      (twoSidedFiniteLaw X P (I.map (Nat.castEmbedding (R := ℤ)))) =
      (P : Measure Ω).map (fun ω ↦ I.restrict (fun n ↦ X n ω)) := by
  let K : Finset ℤ := I.map (Nat.castEmbedding (R := ℤ))
  have hnonneg : ∀ j : K, 0 ≤ (j : ℤ) + 0 := by
    -- Proof comment: embedded natural indices are already nonnegative, so no padding is needed.
    intro j
    rcases Finset.mem_map.mp j.2 with ⟨n, hn, hnj⟩
    simp [hnj.symm]
  have hnormalize :
      twoSidedFiniteLaw X P K = paddedFiniteLaw X P K 0 := by
    -- Proof comment: the common finite law on embedded natural indices reduces to padding `0`.
    unfold twoSidedFiniteLaw
    symm
    exact paddedFiniteLaw_eq_of_le X P hX K (N := 0) (M := leftPadding K) (Nat.zero_le _)
      hnonneg
  calc
    Measure.map (restrictFromEmbeddedNat (E := E) I) (twoSidedFiniteLaw X P K)
        = Measure.map (restrictFromEmbeddedNat (E := E) I) (paddedFiniteLaw X P K 0) := by
          rw [hnormalize]
    _ = (P : Measure Ω).map (fun ω ↦ I.restrict (fun n ↦ X n ω)) := by
          -- Proof comment: after removing the padding, restricting back from the embedded
          -- integer coordinates is exactly the original finite restriction of `X`.
          rw [paddedFiniteLaw]
          have hPathAe :
              AEMeasurable
                (paddedPathRestriction (E := E) K 0 ∘ fun ω n ↦ X n ω)
                (P : Measure Ω) :=
            (measurable_paddedPathRestriction (E := E) K 0).aemeasurable.comp_aemeasurable
              (aemeasurableProcessMap X P hX)
          rw [AEMeasurable.map_map_of_aemeasurable
            (measurable_restrictFromEmbeddedNat (E := E) I).aemeasurable hPathAe]
          apply Measure.map_congr
          filter_upwards [] with ω
          ext i
          simp [restrictFromEmbeddedNat, paddedPathRestriction, K, Finset.restrict]

/-- Helper for Lemma 20.4: translating an integer by its absolute value makes it nonnegative. -/
private theorem selfAddNatAbs_nonneg (z : ℤ) : 0 ≤ z + Int.natAbs z := by
  -- Proof comment: split on the sign of `z` and rewrite `natAbs` to the matching integer form.
  cases le_or_gt 0 z with
  | inl hz =>
      rw [Int.natAbs_of_nonneg hz]
      omega
  | inr hz =>
      have hz' : z ≤ 0 := le_of_lt hz
      rw [Int.ofNat_natAbs_of_nonpos hz']
      omega

/-- Helper for Lemma 20.4: translate integer indices by a fixed shift. -/
private def translateEmbedding (s : ℤ) : ℤ ↪ ℤ where
  toFun := fun j ↦ s + j
  inj' := by
    -- Proof comment: translation by a fixed integer is injective.
    intro a b h
    exact add_left_cancel h

/-- Helper for Lemma 20.4: the finite subset obtained by translating each index by `s`. -/
private def translateFinset (s : ℤ) (I : Finset ℤ) : Finset ℤ :=
  I.map (translateEmbedding s)

/-- Helper for Lemma 20.4: reindex tuples on the translated finite subset back to the original
index set. -/
private def translateTuple (s : ℤ) (I : Finset ℤ) :
    (translateFinset s I → E) → I → E :=
  fun x i ↦ x ⟨s + i, Finset.mem_map.mpr ⟨i, i.2, rfl⟩⟩

/-- Helper for Lemma 20.4: the tuple reindexing map along a translation is measurable. -/
private theorem measurable_translateTuple (s : ℤ) (I : Finset ℤ) :
    Measurable (translateTuple (E := E) s I) := by
  -- Proof comment: each coordinate after reindexing is evaluation at one translated index.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply
    (⟨s + i, Finset.mem_map.mpr ⟨i, i.2, rfl⟩⟩ : translateFinset s I)

/-- Helper for Lemma 20.4: translating the finite index set does not change the resulting
two-sided finite-dimensional law after reindexing back to the original coordinates. -/
private theorem translatedFiniteLaw_eq
    (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω) (hX : IsStationaryProcess X P)
    (s : ℤ) (I : Finset ℤ) :
    Measure.map (translateTuple (E := E) s I)
      (twoSidedFiniteLaw X P (translateFinset s I)) =
      twoSidedFiniteLaw X P I := by
  let J : Finset ℤ := translateFinset s I
  let N : ℕ := leftPadding I + leftPadding J + Int.natAbs s
  let M : ℕ := Int.toNat ((s : ℤ) + N)
  have hsN_nonneg : 0 ≤ (s : ℤ) + N := by
    -- Proof comment: the common padding includes `Int.natAbs s`, so the translated shift
    -- itself is nonnegative after padding.
    dsimp [N]
    have hsAbs : 0 ≤ (s : ℤ) + Int.natAbs s := selfAddNatAbs_nonneg s
    omega
  have hJN : leftPadding J ≤ N := by
    -- Proof comment: the common padding is chosen to dominate the translated set padding.
    dsimp [N]
    omega
  have hIM : leftPadding I ≤ M := by
    -- Proof comment: after reindexing, the translated coordinates become the original
    -- coordinates at the larger padding `M`.
    have hIM' : (leftPadding I : ℤ) ≤ (M : ℤ) := by
      rw [show ((M : ℕ) : ℤ) = (s : ℤ) + N by
        dsimp [M]
        rw [Int.toNat_of_nonneg hsN_nonneg]]
      dsimp [N]
      have hsAbs : 0 ≤ (s : ℤ) + Int.natAbs s := selfAddNatAbs_nonneg s
      omega
    exact_mod_cast hIM'
  have hnormalizeJ :
      twoSidedFiniteLaw X P J = paddedFiniteLaw X P J N := by
    -- Proof comment: increase the translated finite law to the common padding `N`.
    unfold twoSidedFiniteLaw
    exact paddedFiniteLaw_eq_of_le X P hX J hJN
      (fun j ↦ nonneg_add_leftPadding J j.2)
  have hnormalizeI :
      twoSidedFiniteLaw X P I = paddedFiniteLaw X P I M := by
    -- Proof comment: the original finite law is also normalized to the padding induced by the
    -- translated coordinates.
    unfold twoSidedFiniteLaw
    exact paddedFiniteLaw_eq_of_le X P hX I hIM
      (fun j ↦ nonneg_add_leftPadding I j.2)
  have hmap :
      Measure.map (translateTuple (E := E) s I) (paddedFiniteLaw X P J N) =
        paddedFiniteLaw X P I M := by
    rw [paddedFiniteLaw, paddedFiniteLaw]
    have hPathAe :
        AEMeasurable
          (paddedPathRestriction (E := E) J N ∘ fun ω n ↦ X n ω)
          (P : Measure Ω) :=
      (measurable_paddedPathRestriction (E := E) J N).aemeasurable.comp_aemeasurable
        (aemeasurableProcessMap X P hX)
    rw [AEMeasurable.map_map_of_aemeasurable
      (measurable_translateTuple (E := E) s I).aemeasurable hPathAe]
    apply Measure.map_congr
    filter_upwards [] with ω
    ext i
    dsimp [translateTuple, paddedPathRestriction, J, M]
    have hsN_cast : ((Int.toNat ((s : ℤ) + N) : ℕ) : ℤ) = (s : ℤ) + N := by
      rw [Int.toNat_of_nonneg hsN_nonneg]
    have hiM_nonneg : 0 ≤ (i : ℤ) + Int.toNat ((s : ℤ) + N) := by
      rw [hsN_cast]
      dsimp [N]
      have hiN : 0 ≤ (i : ℤ) + leftPadding I := nonneg_add_leftPadding I i.2
      have hsAbs : 0 ≤ (s : ℤ) + Int.natAbs s := selfAddNatAbs_nonneg s
      omega
    have hindex :
        Int.toNat ((s + (i : ℤ)) + N) =
          Int.toNat ((i : ℤ) + Int.toNat ((s : ℤ) + N)) := by
      have hindex' :
          ((Int.toNat ((s + (i : ℤ)) + N) : ℕ) : ℤ) =
            Int.toNat ((i : ℤ) + Int.toNat ((s : ℤ) + N)) := by
        rw [Int.toNat_of_nonneg, Int.toNat_of_nonneg hiM_nonneg, hsN_cast]
        · omega
        · dsimp [N]
          have hiN : 0 ≤ (i : ℤ) + leftPadding I := nonneg_add_leftPadding I i.2
          have hsAbs : 0 ≤ (s : ℤ) + Int.natAbs s := selfAddNatAbs_nonneg s
          omega
      exact_mod_cast hindex'
    rw [hindex]
  calc
    Measure.map (translateTuple (E := E) s I) (twoSidedFiniteLaw X P J)
        = Measure.map (translateTuple (E := E) s I) (paddedFiniteLaw X P J N) := by
          rw [hnormalizeJ]
    _ = paddedFiniteLaw X P I M := hmap
    _ = twoSidedFiniteLaw X P I := by
          rw [← hnormalizeI]

-- Proof sketch: realize the extension on the path space `ℤ → E`, define the finite-dimensional
-- marginals on left-infinite coordinate sets by stationarity of `X`, check consistency, and apply
-- the countable projective-limit theorem to obtain a probability measure on `E^ℤ`.
variable [StandardBorelSpace E]

/-- Lemma 20.4: a stationary process indexed by `ℕ₀` admits a stationary extension indexed by
`ℤ`; equivalently, there exists a probability law on the two-sided path space whose canonical
coordinate process is stationary and whose restriction to the nonnegative coordinates has the same
law as the original process. -/
theorem exists_two_sided_stationary_extension
    (X : ℕ → Ω → E) (P : ProbabilityMeasure Ω)
    (hX : IsStationaryProcess X P) :
    ∃ Pext : ProbabilityMeasure (ℤ → E),
      IsStationaryProcess (fun n ω ↦ ω n) (Pext : Measure (ℤ → E)) ∧
        IdentDistrib
          nonnegativePathRestriction
          (fun ω n ↦ X n ω)
          (Pext : Measure (ℤ → E))
          (P : Measure Ω) := by
  classical
  let Pfin : ∀ J : Finset ℤ, Measure (J → E) := twoSidedFiniteLaw X P
  letI (J : Finset ℤ) : IsProbabilityMeasure (Pfin J) := by
    dsimp [Pfin, twoSidedFiniteLaw, paddedFiniteLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_paddedPathRestriction (E := E) J (leftPadding J)).aemeasurable.comp_aemeasurable
        (aemeasurableProcessMap X P hX))
  have hPfin : IsProjectiveMeasureFamily (α := fun _ : ℤ ↦ E) Pfin :=
    isProjectiveMeasureFamily_twoSidedFiniteLaw X P hX
  rcases existsUnique_probabilityMeasure_isProjectiveLimit_of_countable_standardBorel
      (I := ℤ) (Ω := fun _ : ℤ ↦ E) Pfin hPfin with
    ⟨μext, hμext, -⟩
  let Pext : ProbabilityMeasure (ℤ → E) := ⟨μext, hμext.1⟩
  refine ⟨Pext, ?_, ?_⟩
  · -- Route correction: the remaining blocker is the finite-set translation identity for
    -- `twoSidedFiniteLaw`, needed to turn the projective-limit law on `ℤ` into a stationary
    -- process law. The translated finite-dimensional law is now handled by
    -- `translatedFiniteLaw_eq`, so the remaining step is a finite-dimensional comparison.
    intro s
    have hShiftAe :
        AEMeasurable (fun ω t ↦ ω (s + t)) (Pext : Measure (ℤ → E)) := by
      -- Proof comment: the shifted canonical path is measurable coordinatewise.
      exact (measurable_pi_lambda _ fun t ↦ measurable_pi_apply (s + t)).aemeasurable
    have hIdAe : AEMeasurable (fun ω : ℤ → E ↦ ω) (Pext : Measure (ℤ → E)) :=
      measurable_id.aemeasurable
    rw [ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib
      (T := ℤ)
      (𝓧 := fun _ : ℤ ↦ E)
      (P := (Pext : Measure (ℤ → E)))
      (X := fun t ω ↦ ω (s + t))
      (Y := fun t ω ↦ ω t)
      hShiftAe hIdAe]
    intro I
    let J : Finset ℤ := translateFinset s I
    refine ⟨?_, ?_, ?_⟩
    · -- Proof comment: the finite restriction of the shifted path is measurable coordinatewise.
      exact (Finset.measurable_restrict I).comp_aemeasurable hShiftAe
    · -- Proof comment: the unshifted finite restriction is the canonical projection.
      exact (Finset.measurable_restrict I).aemeasurable
    · have hshiftMap :
          (Pext : Measure (ℤ → E)).map (fun ω ↦ I.restrict (fun t ↦ ω (s + t))) =
            Measure.map (translateTuple (E := E) s I) (Pfin J) := by
        -- Proof comment: finite shifted coordinates factor through the translated index set.
        have hrestrictAe :
            AEMeasurable (J.restrict) (Pext : Measure (ℤ → E)) := by
          exact (Finset.measurable_restrict J).aemeasurable
        calc
          (Pext : Measure (ℤ → E)).map (fun ω ↦ I.restrict (fun t ↦ ω (s + t)))
              = Measure.map (translateTuple (E := E) s I)
                  (Measure.map J.restrict (Pext : Measure (ℤ → E))) := by
                    rw [AEMeasurable.map_map_of_aemeasurable
                      (measurable_translateTuple (E := E) s I).aemeasurable hrestrictAe]
                    apply Measure.map_congr
                    filter_upwards [] with ω
                    ext i
                    simp [translateTuple, J, Finset.restrict]
          _ = Measure.map (translateTuple (E := E) s I) (Pfin J) := by
                simpa [Pext] using congrArg (Measure.map (translateTuple (E := E) s I)) (hμext.2 J)
      calc
        (Pext : Measure (ℤ → E)).map (fun ω ↦ I.restrict (fun t ↦ ω (s + t)))
            = Measure.map (translateTuple (E := E) s I) (Pfin J) := hshiftMap
        _ = twoSidedFiniteLaw X P I := by
              simpa [Pfin, J] using translatedFiniteLaw_eq X P hX s I
        _ = (Pext : Measure (ℤ → E)).map (fun ω ↦ I.restrict (fun t ↦ ω t)) := by
              simpa [Pfin] using (hμext.2 I).symm
  · have hPathMeas : Measurable (nonnegativePathRestriction (E := E)) := by
        -- Proof comment: the restriction to nonnegative coordinates is measurable coordinatewise.
        simpa [nonnegativePathRestriction] using
          (measurable_pi_lambda
            (fun ω : ℤ → E ↦ fun n : ℕ ↦ ω (n : ℤ))
            (fun n ↦ (measurable_pi_apply (n : ℤ) : Measurable fun ω : ℤ → E ↦ ω (n : ℤ))))
    have hPathAe :
        AEMeasurable nonnegativePathRestriction (Pext : Measure (ℤ → E)) :=
      hPathMeas.aemeasurable
    have hProcessAe : AEMeasurable (fun ω n ↦ X n ω) (P : Measure Ω) :=
      aemeasurableProcessMap X P hX
    refine ⟨hPathAe, hProcessAe, ?_⟩
    have hProjLeft :
        IsProjectiveLimit
          ((Pext : Measure (ℤ → E)).map nonnegativePathRestriction)
          (fun I : Finset ℕ ↦ (P : Measure Ω).map (fun ω ↦ I.restrict (fun n ↦ X n ω))) := by
      intro I
      let K : Finset ℤ := I.map (Nat.castEmbedding (R := ℤ))
      have hleft :
          (Pext : Measure (ℤ → E)).map (fun ω ↦ I.restrict (nonnegativePathRestriction ω)) =
            Measure.map (restrictFromEmbeddedNat (E := E) I) (Pfin K) := by
        -- Proof comment: the nonnegative finite restriction factors through the embedded integer
        -- coordinates and the projective-limit identity on `K`.
        have hrestrictAe :
            AEMeasurable (K.restrict) (Pext : Measure (ℤ → E)) := by
          exact (Finset.measurable_restrict K).aemeasurable
        calc
          (Pext : Measure (ℤ → E)).map (fun ω ↦ I.restrict (nonnegativePathRestriction ω))
              = Measure.map (restrictFromEmbeddedNat (E := E) I)
                  (Measure.map K.restrict (Pext : Measure (ℤ → E))) := by
                    rw [AEMeasurable.map_map_of_aemeasurable
                      (measurable_restrictFromEmbeddedNat (E := E) I).aemeasurable hrestrictAe]
                    apply Measure.map_congr
                    filter_upwards [] with ω
                    funext i
                    simp [restrictFromEmbeddedNat, nonnegativePathRestriction, Finset.restrict, K]
          _ = Measure.map (restrictFromEmbeddedNat (E := E) I) (Pfin K) := by
                simpa [Pext] using
                  congrArg (Measure.map (restrictFromEmbeddedNat (E := E) I)) (hμext.2 K)
      calc
        Measure.map I.restrict ((Pext : Measure (ℤ → E)).map nonnegativePathRestriction)
            = (Pext : Measure (ℤ → E)).map (fun ω ↦ I.restrict (nonnegativePathRestriction ω)) := by
                simpa [Function.comp] using
                  (AEMeasurable.map_map_of_aemeasurable
                    (Finset.measurable_restrict I).aemeasurable hPathAe)
        _ = Measure.map (restrictFromEmbeddedNat (E := E) I) (Pfin K) := hleft
        _ = (P : Measure Ω).map (fun ω ↦ I.restrict (fun n ↦ X n ω)) := by
              simpa [Pfin, K] using embeddedNatFiniteLaw_eq_original X P hX I
    exact hProjLeft.unique
      (ProbabilityTheory.isProjectiveLimit_map
        (T := ℕ)
        (𝓧 := fun _ : ℕ ↦ E)
        (P := (P : Measure Ω))
        (X := fun n ω ↦ X n ω)
        hProcessAe)
