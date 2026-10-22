/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_13

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

open scoped BigOperators

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Exercise 24.3.2: permuting a finite coordinate vector by `σ`. -/
private def permuteCoords {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun x i ↦ x (σ i)

/-- Helper for Exercise 24.3.2: merging the last two coordinates of a finite vector. -/
private def mergeLastRaw {n : ℕ} : (Fin (n + 2) → ℝ) → Fin (n + 1) → ℝ :=
  fun x ↦
    Fin.snoc
      (Fin.init (Fin.init x))
      ((Fin.init x) (Fin.last n) + x (Fin.last (n + 1)))

/-- Helper for Exercise 24.3.2: the merged parameter vector adds the last two coordinates. -/
private def mergeLastParams {n : ℕ} (θ : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc
    (Fin.init (Fin.init θ))
    ((Fin.init θ) (Fin.last n) + θ (Fin.last (n + 1)))

/-- The finite-dimensional Dirichlet law obtained by normalizing independent Gamma coordinates
with shape parameters `θ i`. -/
def dirichletMeasure {n : ℕ} (θ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map (fun y i ↦ y i / ∑ j, y j)

-- Proof sketch: unfold `dirichletMeasure`; it is exactly the pushforward of the product Gamma law
-- along the coordinatewise normalization map `y ↦ (fun i ↦ y i / ∑ j, y j)`.
/-- Unfolding `dirichletMeasure` gives the normalized-Gamma construction of the Dirichlet law. -/
theorem dirichletMeasure_def {n : ℕ} (θ : Fin n → ℝ) :
    dirichletMeasure θ =
      (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map (fun y i ↦ y i / ∑ j, y j) := by
  -- Proof comment: this is exactly the local definition of `dirichletMeasure`.
  rfl

/-- Helper for Exercise 24.3.2: permuting the coordinates does not change the total mass. -/
private theorem sum_permuteCoords {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    ∑ j, permuteCoords σ x j = ∑ j, x j := by
  -- Proof comment: finite sums are invariant under reindexing by a permutation.
  simpa [permuteCoords] using (Equiv.sum_comp σ x)

/-- Helper for Exercise 24.3.2: normalizing after permuting Gamma coordinates equals permuting the
normalized vector. -/
private theorem normalize_permuteCoords {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (fun y : Fin n → ℝ ↦ permuteCoords σ (fun i ↦ y i / ∑ j, y j)) =
      fun y ↦ fun i ↦ permuteCoords σ y i / ∑ j, permuteCoords σ y j := by
  -- Proof comment: both sides have the same numerator coordinate, and the denominator is the
  -- permutation-invariant total mass from `sum_permuteCoords`.
  funext y i
  rw [sum_permuteCoords]
  rfl

/-- Helper for Exercise 24.3.2: permuting the independent Gamma coordinates permutes the product
law in the same way. -/
private theorem map_piGamma_permuteCoords {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) (σ : Equiv.Perm (Fin n)) :
    Measure.map (permuteCoords σ) (Measure.pi fun i ↦ gammaMeasure (θ i) 1) =
      Measure.pi fun i ↦ gammaMeasure ((fun i ↦ θ (σ i)) i) 1 := by
  -- Proof comment: `Measure.pi_map_piCongrLeft` is exactly the finite-product reindexing theorem.
  letI : ∀ i : Fin n, IsProbabilityMeasure (gammaMeasure ((fun i ↦ θ (σ i)) i) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hθ (σ i)) zero_lt_one
  have hpermEq :
      permuteCoords σ = ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) σ.symm) := by
    funext x
    ext i
    simp [permuteCoords, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hpermEq]
  simpa using (measurePreserving_piCongrLeft
    (α := fun _ : Fin n ↦ ℝ)
    (μ := fun i : Fin n ↦ gammaMeasure ((fun i ↦ θ (σ i)) i) 1)
    (f := σ.symm)).map_eq

/-- Helper for Exercise 24.3.2: the Dirichlet law is stable under coordinate permutations. -/
private theorem dirichletMeasure_map_permute {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) (σ : Equiv.Perm (Fin n)) :
    Measure.map (permuteCoords σ) (dirichletMeasure θ) =
      dirichletMeasure fun i ↦ θ (σ i) := by
  have hperm_meas : Measurable (permuteCoords σ) := by
    -- Proof comment: permutation just reindexes measurable coordinate projections.
    refine measurable_pi_lambda _ ?_
    intro i
    simpa [permuteCoords] using (measurable_pi_apply (σ i))
  have hnormalize_meas : Measurable (fun y : Fin n → ℝ ↦ fun i ↦ y i / ∑ j, y j) := by
    -- Proof comment: the normalization map is coordinatewise measurable arithmetic.
    fun_prop
  -- Proof comment: move the permutation past the normalization map, then reindex the Gamma
  -- product source measure.
  calc
    Measure.map (permuteCoords σ) (dirichletMeasure θ)
        = Measure.map (permuteCoords σ)
            ((Measure.pi fun i ↦ gammaMeasure (θ i) 1).map
              (fun y i ↦ y i / ∑ j, y j)) := by
              rw [dirichletMeasure_def]
    _ = Measure.map
          (fun y : Fin n → ℝ ↦ permuteCoords σ (fun i ↦ y i / ∑ j, y j))
          (Measure.pi fun i ↦ gammaMeasure (θ i) 1) := by
            simpa [Function.comp] using
              (Measure.map_map
                (μ := Measure.pi fun i ↦ gammaMeasure (θ i) 1)
                hperm_meas hnormalize_meas)
    _ = Measure.map
          (fun y : Fin n → ℝ ↦ fun i ↦ permuteCoords σ y i / ∑ j, permuteCoords σ y j)
          (Measure.pi fun i ↦ gammaMeasure (θ i) 1) := by
            refine Measure.map_congr ?_
            exact Filter.Eventually.of_forall (fun y ↦ by
              simpa using congrFun (normalize_permuteCoords σ) y)
    _ = Measure.map (fun y : Fin n → ℝ ↦ fun i ↦ y i / ∑ j, y j)
          (Measure.map (permuteCoords σ) (Measure.pi fun i ↦ gammaMeasure (θ i) 1)) := by
            simpa [Function.comp] using
              (Measure.map_map
                (μ := Measure.pi fun i ↦ gammaMeasure (θ i) 1)
                hnormalize_meas hperm_meas).symm
    _ = Measure.map (fun y : Fin n → ℝ ↦ fun i ↦ y i / ∑ j, y j)
          (Measure.pi fun i ↦ gammaMeasure ((fun i ↦ θ (σ i)) i) 1) := by
            rw [map_piGamma_permuteCoords θ hθ]
    _ = dirichletMeasure fun i ↦ θ (σ i) := by
          rw [dirichletMeasure_def]

/-- Helper for Exercise 24.3.2: splitting off the last Gamma coordinate turns a finite product
law into the product of the prefix law and the final marginal. -/
private theorem map_pi_splitLast_eq_prod {m : ℕ} (μ : Fin (m + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] :
    ((Measure.pi μ).map (fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m)))) =
      (Measure.pi fun i : Fin m ↦ μ i.castSucc).prod (μ (Fin.last m)) := by
  -- Proof comment: `measurePreserving_piFinSuccAbove` gives the correct factorization; what
  -- remains is a routine rewrite from its `succAbove` indexing to the explicit `castSucc` prefix.
  let splitLast : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ :=
    fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last m)).map_eq
  have hSplitLast : splitLast = Prod.swap ∘ e := by
    -- Proof comment: for `Fin.last`, `succAbove` is `castSucc`, so `piFinSuccAbove` exposes the
    -- final coordinate together with the prefix block.
    funext x
    ext i
    · simp [splitLast, Function.comp, e, Fin.init]
    · simp [splitLast, Function.comp, e]
  -- Proof comment: first factor the product measure through `piFinSuccAbove`, then swap the two
  -- factors so the prefix block comes first.
  calc
    ((Measure.pi μ).map splitLast)
        = (((Measure.pi μ).map e).map Prod.swap) := by
            rw [hSplitLast, Measure.map_map measurable_swap e.measurable]
    _ = (((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i))).map
          Prod.swap) := by rw [hMapEq]
    _ = (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)).prod (μ (Fin.last m)) := by
          rw [Measure.prod_swap]
    _ = (Measure.pi fun i : Fin m ↦ μ i.castSucc).prod (μ (Fin.last m)) := by
          simp [Fin.succAbove_last]

/-- Helper for Exercise 24.3.2: rebuilding a finite vector from a prefix block and its final
coordinate transports the corresponding product law back to the original `Measure.pi`. -/
private theorem map_prod_snoc_eq_pi {m : ℕ} (μ : Fin (m + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] :
    Measure.map (fun p : (Fin m → ℝ) × ℝ ↦ Fin.snoc p.1 p.2)
      ((Measure.pi fun i : Fin m ↦ μ i.castSucc).prod (μ (Fin.last m))) =
        Measure.pi μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last m)).map_eq
  have hsnoc :
      (fun p : (Fin m → ℝ) × ℝ ↦ Fin.snoc p.1 p.2) = e.symm ∘ Prod.swap := by
    -- Proof comment: undoing the last-coordinate split inserts the saved final coordinate back
    -- into the `Fin.snoc` position.
    funext p
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [Function.comp, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.snoc_castSucc]
    · simp [Function.comp, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  -- Proof comment: rewrite the rebuild map as the inverse `piFinSuccAbove` transport followed by
  -- `Prod.swap`, then cancel it against the canonical split map.
  calc
    Measure.map (fun p : (Fin m → ℝ) × ℝ ↦ Fin.snoc p.1 p.2)
        ((Measure.pi fun i : Fin m ↦ μ i.castSucc).prod (μ (Fin.last m)))
        = Measure.map e.symm
            (Measure.map Prod.swap
              ((Measure.pi fun i : Fin m ↦ μ i.castSucc).prod (μ (Fin.last m)))) := by
              rw [hsnoc, Measure.map_map e.symm.measurable measurable_swap]
    _ = Measure.map e.symm
          ((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ i.castSucc)) := by
            rw [Measure.prod_swap]
    _ = Measure.map e.symm
          ((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i))) := by
            simp [Fin.succAbove_last]
    _ = Measure.pi μ := by
          rw [← hMapEq, MeasurableEquiv.map_symm_map]

/-- Helper for Exercise 24.3.2: adding the two tail coordinates in a product law leaves the
prefix block untouched and convolves the tail marginals. -/
private theorem map_prod_tailAdd_eq_prod_conv {m : ℕ} (μ : Measure (Fin m → ℝ))
    (ν ρ : Measure ℝ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    Measure.map (fun p : (Fin m → ℝ) × (ℝ × ℝ) ↦ (p.1, p.2.1 + p.2.2))
      (μ.prod (ν.prod ρ)) = μ.prod (ν ∗ ρ) := by
  -- Proof comment: this is `Measure.map_prod_map` with the identity on the prefix block and the
  -- addition map on the tail pair.
  simpa [Measure.conv] using
    (Measure.map_prod_map μ (ν.prod ρ) measurable_id measurable_add).symm

/-- Helper for Exercise 24.3.2: merging the last two normalized coordinates agrees with first
merging the raw Gamma coordinates and then normalizing. -/
private theorem mergeLastNormalized_eq_normalize_mergeLastRaw {n : ℕ} :
    (fun y : Fin (n + 2) → ℝ ↦
      mergeLastRaw (fun i ↦ y i / ∑ j, y j)) =
      fun y ↦ fun i ↦ mergeLastRaw y i / ∑ j, mergeLastRaw y j := by
  -- Proof comment: the merged numerator is the sum of the two normalized tail coordinates, while
  -- the merged denominator is exactly the unchanged total mass.
  funext y
  apply funext
  intro i
  have hsum :
      ∑ j, mergeLastRaw y j = ∑ j, y j := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    rw [show (∑ i : Fin (n + 1), y i.castSucc) =
        (∑ x : Fin n, y x.castSucc.castSucc) + y (Fin.last n).castSucc by
      simpa using (Fin.sum_univ_castSucc (fun i : Fin (n + 1) => y i.castSucc))]
    simp [mergeLastRaw, Fin.init, add_assoc, add_comm, add_left_comm]
  -- Proof comment: with the total mass identified, the coordinate formulas agree by cases on the
  -- final coordinate.
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [hsum]
    simp [mergeLastRaw, Fin.init]
  · rw [hsum]
    simp [mergeLastRaw, Fin.init, add_div]

/-- Helper for Exercise 24.3.2: after splitting the last two raw Gamma coordinates, adding them
replaces the tail pair by a single Gamma law with summed shape. -/
private theorem map_mergeLastRaw_piGamma_eq_piGammaMerged {n : ℕ}
    (θ : Fin (n + 2) → ℝ) (hθ : ∀ i, 0 < θ i) :
    Measure.map mergeLastRaw (Measure.pi fun i : Fin (n + 2) ↦ gammaMeasure (θ i) 1) =
      Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (mergeLastParams θ i) 1 := by
  -- Proof comment: split the source product into prefix and last-tail Gamma coordinates, rewrite
  -- the tail sum as a Gamma convolution, and reassemble the finite product.
  let μ : Fin (n + 2) → Measure ℝ := fun i ↦ gammaMeasure (θ i) 1
  letI : ∀ i : Fin (n + 2), IsProbabilityMeasure (μ i) := fun i ↦ by
    dsimp [μ]
    exact isProbabilityMeasure_gammaMeasure (hθ i) zero_lt_one
  let prefixMeasure1 : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi fun i : Fin (n + 1) ↦ μ i.castSucc
  let prefixMeasure : Measure (Fin n → ℝ) :=
    Measure.pi fun i : Fin n ↦ μ i.castSucc.castSucc
  let penultMeasure : Measure ℝ := μ ((Fin.last n).castSucc)
  let lastMeasure : Measure ℝ := μ (Fin.last (n + 1))
  let splitOuter : (Fin (n + 2) → ℝ) → (Fin (n + 1) → ℝ) × ℝ :=
    fun x ↦ (Fin.init x, x (Fin.last (n + 1)))
  let splitInner : (Fin (n + 1) → ℝ) → (Fin n → ℝ) × ℝ :=
    fun x ↦ (Fin.init x, x (Fin.last n))
  let splitMiddle : (Fin (n + 1) → ℝ) × ℝ → ((Fin n → ℝ) × ℝ) × ℝ :=
    fun p ↦ (splitInner p.1, p.2)
  let associate : ((Fin n → ℝ) × ℝ) × ℝ → (Fin n → ℝ) × (ℝ × ℝ) :=
    MeasurableEquiv.prodAssoc
  let splitTail : (Fin (n + 2) → ℝ) → (Fin n → ℝ) × (ℝ × ℝ) :=
    fun x ↦ (Fin.init (Fin.init x), ((Fin.init x) (Fin.last n), x (Fin.last (n + 1))))
  let tailAdd : (Fin n → ℝ) × (ℝ × ℝ) → (Fin n → ℝ) × ℝ :=
    fun p ↦ (p.1, p.2.1 + p.2.2)
  let rebuild : (Fin n → ℝ) × ℝ → Fin (n + 1) → ℝ :=
    fun q ↦ Fin.snoc q.1 q.2
  let mergeTail : (Fin (n + 2) → ℝ) → (Fin n → ℝ) × ℝ :=
    fun x ↦ tailAdd (splitTail x)
  letI : SFinite prefixMeasure1 := by infer_instance
  letI : SFinite prefixMeasure := by infer_instance
  letI : SFinite penultMeasure := by infer_instance
  letI : SFinite lastMeasure := by infer_instance
  have hsplitOuter :
      Measure.map splitOuter (Measure.pi μ) = prefixMeasure1.prod lastMeasure := by
    -- Proof comment: first separate the final raw Gamma coordinate from the first `n + 1`.
    simpa [μ, prefixMeasure1, lastMeasure, splitOuter, Fin.init] using
      (map_pi_splitLast_eq_prod (μ := μ))
  have hsplitInner :
      Measure.map splitInner prefixMeasure1 = prefixMeasure.prod penultMeasure := by
    -- Proof comment: then split the remaining `n + 1` block into the first `n` coordinates and
    -- the penultimate raw Gamma coordinate.
    simpa [μ, prefixMeasure1, prefixMeasure, penultMeasure, splitInner, Fin.init] using
      (map_pi_splitLast_eq_prod (μ := fun i : Fin (n + 1) ↦ μ i.castSucc))
  have hsplitTail :
      Measure.map splitTail (Measure.pi μ) =
        prefixMeasure.prod (penultMeasure.prod lastMeasure) := by
    have hsplitInner_meas : Measurable splitInner := by
      -- Proof comment: `splitInner` is just a projection to the prefix block and last entry.
      fun_prop
    have hsplitMiddle_meas : Measurable splitMiddle := by
      -- Proof comment: this only applies `splitInner` to the first factor and keeps the last
      -- coordinate unchanged.
      fun_prop
    have hsplitTail_comp :
        splitTail = associate ∘ splitMiddle ∘ splitOuter := by
      -- Proof comment: `splitTail` performs the two successive coordinate splits and then
      -- reassociates the resulting nested product.
      funext x
      ext i <;> rfl
    have hsplitTailStep1 :
        Measure.map splitTail (Measure.pi μ) =
          Measure.map (associate ∘ splitMiddle)
            (Measure.map splitOuter (Measure.pi μ)) := by
      rw [hsplitTail_comp]
      simpa [Function.comp] using
        (Measure.map_map
          (μ := Measure.pi μ)
          (f := splitOuter)
          (g := associate ∘ splitMiddle)
          (by fun_prop)
          (by fun_prop)).symm
    have hsplitTailStep2 :
        Measure.map (associate ∘ splitMiddle)
            (Measure.map splitOuter (Measure.pi μ)) =
          Measure.map associate
            (Measure.map splitMiddle
              (Measure.map splitOuter (Measure.pi μ))) := by
      simpa [Function.comp] using
        (Measure.map_map
          (μ := Measure.map splitOuter (Measure.pi μ))
          (f := splitMiddle)
          (g := associate)
          (by fun_prop)
          hsplitMiddle_meas).symm
    have hmiddleProd :
        Measure.map splitMiddle
            (prefixMeasure1.prod lastMeasure) =
          (Measure.map splitInner prefixMeasure1).prod lastMeasure := by
      simpa using
        (Measure.map_prod_map prefixMeasure1 lastMeasure hsplitInner_meas measurable_id).symm
    calc
      Measure.map splitTail (Measure.pi μ)
          = Measure.map associate
              (Measure.map splitMiddle
                (Measure.map splitOuter (Measure.pi μ))) := by
                  rw [hsplitTailStep1, hsplitTailStep2]
      _ = Measure.map associate
            (Measure.map splitMiddle
              (prefixMeasure1.prod lastMeasure)) := by
              rw [hsplitOuter]
      _ = Measure.map associate
            ((Measure.map splitInner prefixMeasure1).prod lastMeasure) := by
            rw [hmiddleProd]
      _ = Measure.map associate
            ((prefixMeasure.prod penultMeasure).prod lastMeasure) := by
            rw [hsplitInner]
      _ = prefixMeasure.prod (penultMeasure.prod lastMeasure) := by
            simpa using
              (Measure.prodAssoc_prod
                (μ := prefixMeasure)
                (ν := penultMeasure)
                (τ := lastMeasure))
  have htail :
      Measure.map (fun p : (Fin n → ℝ) × (ℝ × ℝ) ↦ (p.1, p.2.1 + p.2.2))
          (prefixMeasure.prod (penultMeasure.prod lastMeasure)) =
        prefixMeasure.prod (gammaMeasure (mergeLastParams θ (Fin.last n)) 1) := by
    -- Proof comment: only the last two Gamma coordinates interact; their sum has the Gamma law
    -- with summed shape, while the prefix block stays independent.
    calc
      Measure.map (fun p : (Fin n → ℝ) × (ℝ × ℝ) ↦ (p.1, p.2.1 + p.2.2))
          (prefixMeasure.prod (penultMeasure.prod lastMeasure))
          = prefixMeasure.prod (penultMeasure ∗ lastMeasure) := by
              simpa using
                map_prod_tailAdd_eq_prod_conv prefixMeasure penultMeasure lastMeasure
      _ = prefixMeasure.prod (gammaMeasure (mergeLastParams θ (Fin.last n)) 1) := by
            congr 1
            dsimp [penultMeasure, lastMeasure, μ]
            simpa [mergeLastParams] using
              (gammaMeasure_conv_same_rate 1
                (θ ((Fin.last n).castSucc))
                (θ (Fin.last (n + 1)))
                zero_lt_one
                (hθ ((Fin.last n).castSucc))
                (hθ (Fin.last (n + 1))))
  have hmerge_comp :
      mergeLastRaw = rebuild ∘ mergeTail := by
    -- Proof comment: `mergeLastRaw` is exactly "split the last two coordinates, add them, then
    -- rebuild the tuple with the merged terminal coordinate".
    funext x
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [mergeLastRaw, splitTail, tailAdd, rebuild, mergeTail, Fin.init]
    · simp [mergeLastRaw, splitTail, tailAdd, rebuild, mergeTail, Fin.init]
  have hmergeTail_comp : mergeTail = tailAdd ∘ splitTail := by
    rfl
  have hrebuild_meas : Measurable rebuild := by
    -- Proof comment: rebuilding with `Fin.snoc` is coordinatewise measurable.
    refine measurable_pi_lambda _ ?_
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa [rebuild] using (measurable_pi_apply j).comp measurable_fst
    · simpa [rebuild] using measurable_snd
  have htailAdd_meas : Measurable tailAdd := by
    -- Proof comment: this map is identity on the prefix block and addition on the tail pair.
    fun_prop
  have hmergeTail_meas : Measurable mergeTail := by
    -- Proof comment: `mergeTail` first exposes the last two coordinates and then adds them.
    fun_prop
  have hmergeStep1 :
      Measure.map (rebuild ∘ mergeTail) (Measure.pi μ) =
        Measure.map rebuild (Measure.map mergeTail (Measure.pi μ)) := by
    simpa [Function.comp] using
      (Measure.map_map
        (μ := Measure.pi μ)
        (f := mergeTail)
        (g := rebuild)
        hrebuild_meas
        hmergeTail_meas).symm
  have hmergeStep2 :
      Measure.map mergeTail (Measure.pi μ) =
        Measure.map tailAdd (Measure.map splitTail (Measure.pi μ)) := by
    rw [hmergeTail_comp]
    simpa [Function.comp] using
      (Measure.map_map
        (μ := Measure.pi μ)
        (f := splitTail)
        (g := tailAdd)
        htailAdd_meas
        (by fun_prop : Measurable splitTail)).symm
  letI : ∀ i : Fin (n + 1), IsProbabilityMeasure
      (gammaMeasure (mergeLastParams θ i) 1) := fun i ↦ by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa [mergeLastParams, Fin.snoc_castSucc] using
        isProbabilityMeasure_gammaMeasure (hθ j.castSucc.castSucc) zero_lt_one
    · simpa [mergeLastParams] using
        isProbabilityMeasure_gammaMeasure
          (add_pos (hθ ((Fin.last n).castSucc)) (hθ (Fin.last (n + 1))))
          zero_lt_one
  calc
    Measure.map mergeLastRaw (Measure.pi μ)
        = Measure.map rebuild
            (Measure.map mergeTail (Measure.pi μ)) := by
                rw [hmerge_comp]
                rw [hmergeStep1]
    _ = Measure.map rebuild
          (Measure.map tailAdd
            (Measure.map splitTail (Measure.pi μ))) := by
              rw [hmergeStep2]
    _ = Measure.map rebuild
          (Measure.map tailAdd
            (prefixMeasure.prod (penultMeasure.prod lastMeasure))) := by
              rw [hsplitTail]
    _ = Measure.map rebuild
          (prefixMeasure.prod (gammaMeasure (mergeLastParams θ (Fin.last n)) 1)) := by
            rw [htail]
    _ = Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (mergeLastParams θ i) 1 := by
          simpa [μ, prefixMeasure, mergeLastParams, Fin.snoc_castSucc] using
            (map_prod_snoc_eq_pi
              (μ := fun i : Fin (n + 1) ↦ gammaMeasure (mergeLastParams θ i) 1))

/-- Helper for Exercise 24.3.2: merging the last two coordinates pushes the Dirichlet law forward
to the Dirichlet law with merged last parameter. -/
private theorem dirichletMeasure_map_mergeLast {n : ℕ}
    (θ : Fin (n + 2) → ℝ) (hθ : ∀ i, 0 < θ i) :
    Measure.map mergeLastRaw (dirichletMeasure θ) =
      dirichletMeasure (mergeLastParams θ) := by
  have hmerge_meas : Measurable (@mergeLastRaw n) := by
    -- Proof comment: the merge map uses coordinate projections and one addition in the last slot.
    refine measurable_pi_lambda _ ?_
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa [mergeLastRaw, Fin.init] using (measurable_pi_apply j.castSucc.castSucc)
    · simpa [mergeLastRaw, Fin.init] using
        (measurable_pi_apply (Fin.last n).castSucc).add
          (measurable_pi_apply (Fin.last (n + 1)))
  have hnormalize_meas : Measurable (fun y : Fin (n + 2) → ℝ ↦ fun i ↦ y i / ∑ j, y j) := by
    -- Proof comment: the normalization map is measurable coordinatewise arithmetic.
    fun_prop
  have hnormalizeMerged_meas :
      Measurable (fun y : Fin (n + 1) → ℝ ↦ fun i ↦ y i / ∑ j, y j) := by
    -- Proof comment: the same normalization formula is measurable on the merged coordinate space.
    fun_prop
  -- Proof comment: move the merge map through normalization, then invoke the raw Gamma-product
  -- merge law.
  calc
    Measure.map mergeLastRaw (dirichletMeasure θ)
        = Measure.map mergeLastRaw
            ((Measure.pi fun i : Fin (n + 2) ↦ gammaMeasure (θ i) 1).map
              (fun y i ↦ y i / ∑ j, y j)) := by
              rw [dirichletMeasure_def]
    _ = Measure.map
          (fun y : Fin (n + 2) → ℝ ↦ mergeLastRaw (fun i ↦ y i / ∑ j, y j))
          (Measure.pi fun i : Fin (n + 2) ↦ gammaMeasure (θ i) 1) := by
            simpa [Function.comp] using
              (Measure.map_map
                (μ := Measure.pi fun i : Fin (n + 2) ↦ gammaMeasure (θ i) 1)
                hmerge_meas hnormalize_meas)
    _ = Measure.map
          (fun y : Fin (n + 2) → ℝ ↦ fun i ↦ mergeLastRaw y i / ∑ j, mergeLastRaw y j)
          (Measure.pi fun i : Fin (n + 2) ↦ gammaMeasure (θ i) 1) := by
            refine Measure.map_congr ?_
            exact Filter.Eventually.of_forall (fun y ↦ by
              simpa using congrFun (mergeLastNormalized_eq_normalize_mergeLastRaw (n := n)) y)
    _ = Measure.map (fun y : Fin (n + 1) → ℝ ↦ fun i ↦ y i / ∑ j, y j)
          (Measure.map mergeLastRaw (Measure.pi fun i : Fin (n + 2) ↦ gammaMeasure (θ i) 1)) := by
            simpa [Function.comp] using
              (Measure.map_map
                (μ := Measure.pi fun i : Fin (n + 2) ↦ gammaMeasure (θ i) 1)
                hnormalizeMerged_meas hmerge_meas).symm
    _ = Measure.map (fun y : Fin (n + 1) → ℝ ↦ fun i ↦ y i / ∑ j, y j)
          (Measure.pi fun i : Fin (n + 1) ↦ gammaMeasure (mergeLastParams θ i) 1) := by
            rw [map_mergeLastRaw_piGamma_eq_piGammaMerged θ hθ]
    _ = dirichletMeasure (mergeLastParams θ) := by
          rw [dirichletMeasure_def]

-- Proof sketch: realize `X` by the normalized-Gamma construction of the Dirichlet law, then
-- permute the independent Gamma coordinates. The product Gamma law is invariant under coordinate
-- permutations, so pushing forward by the same normalization yields the Dirichlet law with the
-- permuted parameter vector.
/-- First clause of Exercise 24.3.2: permuting the coordinates of a Dirichlet-distributed vector
permutes the parameter vector in the same way. -/
theorem hasLaw_dirichlet_permute
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin n → ℝ}
    {θ : Fin n → ℝ} (hθ : ∀ i, 0 < θ i) (σ : Equiv.Perm (Fin n))
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw (fun ω i ↦ X ω (σ i)) (dirichletMeasure fun i ↦ θ (σ i)) μ := by
  -- Proof comment: compose the Dirichlet realization of `X` with the coordinate permutation.
  simpa [Function.comp, permuteCoords] using
    (HasLaw.comp
      (⟨(show AEMeasurable (permuteCoords σ) (dirichletMeasure θ) from
          (show Measurable (permuteCoords σ) from by
            refine measurable_pi_lambda _ ?_
            intro i
            simpa [permuteCoords] using (measurable_pi_apply (σ i))).aemeasurable),
        dirichletMeasure_map_permute θ hθ σ⟩ :
        HasLaw (permuteCoords σ) (dirichletMeasure fun i ↦ θ (σ i)) (dirichletMeasure θ))
      hX)

-- Proof sketch: write `X` as normalized independent Gamma coordinates with shapes `θ i`. Group
-- the last two Gamma variables into their sum, use Gamma-additivity to identify the new last
-- shape as `θ_{n+1} + θ_{n+2}`, and normalize again to obtain the Dirichlet law of the merged
-- vector.
/-- Second clause of Exercise 24.3.2: combining the last two coordinates of a Dirichlet-
distributed `(n + 2)`-tuple produces a Dirichlet-distributed `(n + 1)`-tuple whose last
parameter is the sum of the last two parameters. -/
theorem hasLaw_dirichlet_merge_last
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 2) → ℝ}
    {θ : Fin (n + 2) → ℝ} (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw
      (fun ω ↦
        Fin.snoc
          (Fin.init (Fin.init (X ω)))
          ((Fin.init (X ω)) (Fin.last n) + X ω (Fin.last (n + 1))))
      (dirichletMeasure <|
        Fin.snoc
          (Fin.init (Fin.init θ))
          ((Fin.init θ) (Fin.last n) + θ (Fin.last (n + 1)))) μ := by
  -- Proof comment: compose the Dirichlet realization with the merge-last coordinate map, then use
  -- the measure-level pushforward identity for `dirichletMeasure`.
  simpa [Function.comp, mergeLastRaw, mergeLastParams] using
    (HasLaw.comp
      (⟨(show AEMeasurable mergeLastRaw (dirichletMeasure θ) from
          (show Measurable mergeLastRaw from by
            refine measurable_pi_lambda _ ?_
            intro i
            rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
            · simpa [mergeLastRaw, Fin.init] using (measurable_pi_apply j.castSucc.castSucc)
            · simpa [mergeLastRaw, Fin.init] using
                (measurable_pi_apply (Fin.last n).castSucc).add
                  (measurable_pi_apply (Fin.last (n + 1)))).aemeasurable),
        by simpa [mergeLastRaw, mergeLastParams] using dirichletMeasure_map_mergeLast θ hθ⟩ :
        HasLaw mergeLastRaw (dirichletMeasure (mergeLastParams θ)) (dirichletMeasure θ))
      hX)

-- Proof comment: package the two source-facing clauses under the single item label so the file
-- exposes Exercise 24.3.2 through one label-associated declaration.
/-- Exercise 24.3.2: permuting Dirichlet coordinates permutes the parameter vector, and merging
the last two coordinates adds the last two Dirichlet parameters. -/
theorem «hasLaw_dirichlet_permute / hasLaw_dirichlet_merge_last» :
    (∀ {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin n → ℝ}
      {θ : Fin n → ℝ}, (∀ i, 0 < θ i) → (σ : Equiv.Perm (Fin n)) →
        HasLaw X (dirichletMeasure θ) μ →
          HasLaw (fun ω i ↦ X ω (σ i)) (dirichletMeasure fun i ↦ θ (σ i)) μ) ∧
      (∀ {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 2) → ℝ}
        {θ : Fin (n + 2) → ℝ}, (∀ i, 0 < θ i) →
          HasLaw X (dirichletMeasure θ) μ →
            HasLaw
              (fun ω ↦
                Fin.snoc
                  (Fin.init (Fin.init (X ω)))
                  ((Fin.init (X ω)) (Fin.last n) + X ω (Fin.last (n + 1))))
              (dirichletMeasure <|
                Fin.snoc
                  (Fin.init (Fin.init θ))
                  ((Fin.init θ) (Fin.last n) + θ (Fin.last (n + 1)))) μ) := by
  constructor
  · intro n μ _ X θ hθ σ hX
    exact hasLaw_dirichlet_permute hθ σ hX
  · intro n μ _ X θ hθ hX
    exact hasLaw_dirichlet_merge_last hθ hX

end ProbabilityTheory
