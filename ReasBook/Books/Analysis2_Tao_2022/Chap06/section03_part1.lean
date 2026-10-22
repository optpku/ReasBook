/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap06
section Section03

open scoped Topology

/-- The one-sided directional difference quotient of `f` on `E` at `x₀` in direction `v`. -/
noncomputable def oneSidedDirectionalDifferenceQuotientWithin
    {n m : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (f : E → EuclideanSpace ℝ (Fin m))
    (x₀ : E)
    (v : EuclideanSpace ℝ (Fin n)) :
    ℝ → EuclideanSpace ℝ (Fin m) :=
  letI : DecidablePred (fun x : EuclideanSpace ℝ (Fin n) => x ∈ E) :=
    Classical.decPred _
  fun t =>
    if ht : ((x₀ : EuclideanSpace ℝ (Fin n)) + t • v) ∈ E then
      t⁻¹ • (f ⟨(x₀ : EuclideanSpace ℝ (Fin n)) + t • v, ht⟩ - f x₀)
    else
      0

/-- Definition 6.9: `f` is one-sided directionally differentiable at the interior point `x₀` in
the direction `v` if the limit of the difference quotient along `t → 0` with `t > 0` and
`x₀ + t v ∈ E` exists. -/
def oneSidedDirectionallyDifferentiableWithinAt
    {n m : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (f : E → EuclideanSpace ℝ (Fin m))
    (x₀ : E)
    (v : EuclideanSpace ℝ (Fin n)) : Prop :=
  ((x₀ : EuclideanSpace ℝ (Fin n)) ∈ interior E) ∧
    ∃ L : EuclideanSpace ℝ (Fin m),
      Filter.Tendsto (oneSidedDirectionalDifferenceQuotientWithin E f x₀ v)
        (nhdsWithin (0 : ℝ)
          {t : ℝ | 0 < t ∧ ((x₀ : EuclideanSpace ℝ (Fin n)) + t • v) ∈ E})
        (𝓝 L)

/-- The one-sided directional derivative `Dᵥ f(x₀)` as the limit value, assuming the directional
derivative exists in the sense of one-sided directional differentiability. -/
noncomputable def oneSidedDirectionalDerivWithin
    {n m : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (f : E → EuclideanSpace ℝ (Fin m))
    (x₀ : E)
    (v : EuclideanSpace ℝ (Fin n))
    (h : oneSidedDirectionallyDifferentiableWithinAt E f x₀ v) :
    EuclideanSpace ℝ (Fin m) :=
  Classical.choose h.2

/-- Helper for Lemma 6.6: if `x₀` is an interior point of `E`, then `t = 0` belongs to the
directional-constraint set `{t | x₀ + t • v ∈ E}`. -/
lemma helperForLemma_6_6_zero_mem_directionConstraint
    {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E) :
    (0 : ℝ) ∈ {t : ℝ | x₀ + t • v ∈ E} := by
  have hx₀E : x₀ ∈ E := interior_subset hx₀
  simpa [hx₀E]

/-- Helper for Lemma 6.6: a `nhdsWithin` limit at `0` over a set containing `0` fixes the
function value at `0`. -/
lemma helperForLemma_6_6_tendsto_nhdsWithin_zero_forces_value
    {m : ℕ}
    {s : Set ℝ}
    {g : ℝ → EuclideanSpace ℝ (Fin m)}
    {L : EuclideanSpace ℝ (Fin m)}
    (hs : (0 : ℝ) ∈ s)
    (hlim : Filter.Tendsto g (nhdsWithin (0 : ℝ) s) (𝓝 L)) :
    g 0 = L := by
  have hpure : Filter.Tendsto g (pure (0 : ℝ)) (𝓝 L) :=
    hlim.comp (pure_le_nhdsWithin hs)
  have hzero : Filter.Tendsto g (pure (0 : ℝ)) (𝓝 (g 0)) :=
    tendsto_pure_nhds g 0
  exact tendsto_nhds_unique hzero hpure

/-- Helper for Lemma 6.6: the directional difference quotient in the theorem statement has value
`0` at `t = 0`. -/
lemma helperForLemma_6_6_differenceQuotient_valueAtZero
    {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)} :
    (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) 0 = 0 := by
  simp

/-- Helper for Lemma 6.6: any limit claim in the theorem's unpunctured `nhdsWithin` filter forces
the claimed limit value to be `0`. -/
lemma helperForLemma_6_6_unpunctured_limit_forces_zero
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hlim : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) :
    f' v = 0 := by
  have hzeroMem : (0 : ℝ) ∈ {t : ℝ | x₀ + t • v ∈ E} :=
    helperForLemma_6_6_zero_mem_directionConstraint (x₀ := x₀) (v := v) hx₀
  have hvalueAtZero :
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) 0 = f' v :=
    helperForLemma_6_6_tendsto_nhdsWithin_zero_forces_value
      (s := {t : ℝ | x₀ + t • v ∈ E}) hzeroMem hlim
  have hquotientAtZero :
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) 0 = 0 :=
    helperForLemma_6_6_differenceQuotient_valueAtZero (f := f) (x₀ := x₀) (v := v)
  calc
    f' v = (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) 0 := hvalueAtZero.symm
    _ = 0 := hquotientAtZero

/-- Helper for Lemma 6.6: if `f' v ≠ 0`, then the theorem's unpunctured directional-limit
statement cannot hold. -/
lemma helperForLemma_6_6_no_unpunctured_limit_of_ne_zero
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hv : f' v ≠ 0) :
    ¬ Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  intro hlim
  have hzero : f' v = 0 :=
    helperForLemma_6_6_unpunctured_limit_forces_zero (x₀ := x₀) (v := v) (f' := f') hx₀ hlim
  exact hv hzero

/-- Helper for Lemma 6.6: the identity map has derivative `id` within `univ` at every point. -/
lemma helperForLemma_6_6_id_hasFDerivWithinAt_univ
    {n : ℕ}
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    HasFDerivWithinAt
      (fun x : EuclideanSpace ℝ (Fin n) => x)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
      x₀ := by
  exact
    ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).hasFDerivAt).hasFDerivWithinAt

/-- Helper for Lemma 6.6: for nonzero `t`, the identity-map directional quotient simplifies
to the direction vector `v`. -/
lemma helperForLemma_6_6_identity_differenceQuotient_of_ne_zero
    {n : ℕ}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {t : ℝ}
    (ht : t ≠ 0) :
    t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin n) => x) (x₀ + t • v) -
      (fun x : EuclideanSpace ℝ (Fin n) => x) x₀) = v := by
  calc
    t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin n) => x) (x₀ + t • v) -
        (fun x : EuclideanSpace ℝ (Fin n) => x) x₀)
        = t⁻¹ • (t • v) := by simp
    _ = (t⁻¹ * t) • v := by simp [smul_smul]
    _ = v := by simp [ht]

/-- Helper for Lemma 6.6: the identity map has the expected punctured directional limit
`t → 0, t ≠ 0`, namely `v`. -/
lemma helperForLemma_6_6_identity_punctured_directional_limit
    {n : ℕ}
    {x₀ v : EuclideanSpace ℝ (Fin n)} :
    Filter.Tendsto
      (fun t : ℝ =>
        t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin n) => x) (x₀ + t • v) -
          (fun x : EuclideanSpace ℝ (Fin n) => x) x₀))
      (𝓝[≠] (0 : ℝ))
      (𝓝 v) := by
  have hfdAt :
      HasFDerivAt
        (fun x : EuclideanSpace ℝ (Fin n) => x)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
        x₀ :=
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).hasFDerivAt
  have hline :
      HasLineDerivAt ℝ
        (fun x : EuclideanSpace ℝ (Fin n) => x)
        ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v)
        x₀
        v :=
    hfdAt.hasLineDerivAt v
  simpa using hline.tendsto_slope_zero

/-- Helper for Lemma 6.6: for nonzero direction `v`, the theorem's unpunctured directional-limit
conclusion fails for the identity map on `ℝⁿ`. -/
lemma helperForLemma_6_6_unpunctured_identity_limit_impossible
    {n : ℕ}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    (hv : v ≠ 0) :
    ¬ Filter.Tendsto
      (fun t : ℝ =>
        t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin n) => x) (x₀ + t • v) -
          (fun x : EuclideanSpace ℝ (Fin n) => x) x₀))
      (nhdsWithin (0 : ℝ)
        {t : ℝ | x₀ + t • v ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))})
      (𝓝 ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v)) := by
  have hx₀ : x₀ ∈ interior (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [interior_univ]
  simpa using
    (helperForLemma_6_6_no_unpunctured_limit_of_ne_zero
      (E := (Set.univ : Set (EuclideanSpace ℝ (Fin n))))
      (f := fun x : EuclideanSpace ℝ (Fin n) => x)
      (x₀ := x₀)
      (v := v)
      (f' := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      hx₀
      hv)

/-- Helper for Lemma 6.6: for any nonzero direction, the identity map on `univ` provides
concrete derivative data together with failure of the unpunctured directional-limit conclusion. -/
lemma helperForLemma_6_6_identity_counterexample_data
    {n : ℕ}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    (hv : v ≠ 0) :
    ∃ hfd : HasFDerivWithinAt
      (fun x : EuclideanSpace ℝ (Fin n) => x)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
      x₀,
      ¬ Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin n) => x) (x₀ + t • v) -
            (fun x : EuclideanSpace ℝ (Fin n) => x) x₀))
        (nhdsWithin (0 : ℝ)
          {t : ℝ | x₀ + t • v ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))})
        (𝓝 ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v)) := by
  refine ⟨helperForLemma_6_6_id_hasFDerivWithinAt_univ (x₀ := x₀), ?_⟩
  exact helperForLemma_6_6_unpunctured_identity_limit_impossible
    (x₀ := x₀)
    (v := v)
    hv

/-- Helper for Lemma 6.6: in dimension `1`, the standard basis direction `e₀` is nonzero. -/
lemma helperForLemma_6_6_standardBasisVector_finOne_ne_zero :
    ((EuclideanSpace.single ⟨0, by decide⟩ (1 : ℝ)) : EuclideanSpace ℝ (Fin 1)) ≠ 0 := by
  intro hzero
  have hcoord :
      ((EuclideanSpace.single ⟨0, by decide⟩ (1 : ℝ)) : EuclideanSpace ℝ (Fin 1))
        ⟨0, by decide⟩ = 0 := by
    simpa using congrArg (fun w : EuclideanSpace ℝ (Fin 1) => w ⟨0, by decide⟩) hzero
  have hone_eq_zero : (1 : ℝ) = 0 := by
    simpa using hcoord
  exact one_ne_zero hone_eq_zero

/-- Helper for Lemma 6.6: there is a concrete dimension-`1` counterexample witness to the
unpunctured directional-limit claim (identity map on `univ` and direction `e₀`). -/
lemma helperForLemma_6_6_unpunctured_identity_counterexample_finOne :
    ∃ x₀ v : EuclideanSpace ℝ (Fin 1),
      ¬ Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin 1) => x) (x₀ + t • v) -
            (fun x : EuclideanSpace ℝ (Fin 1) => x) x₀))
        (nhdsWithin (0 : ℝ)
          {t : ℝ | x₀ + t • v ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 1)))})
        (𝓝 ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) v)) := by
  refine ⟨0, (EuclideanSpace.single ⟨0, by decide⟩ (1 : ℝ) : EuclideanSpace ℝ (Fin 1)), ?_⟩
  exact helperForLemma_6_6_unpunctured_identity_limit_impossible
    (x₀ := (0 : EuclideanSpace ℝ (Fin 1)))
    (v := (EuclideanSpace.single ⟨0, by decide⟩ (1 : ℝ) : EuclideanSpace ℝ (Fin 1)))
    helperForLemma_6_6_standardBasisVector_finOne_ne_zero

/-- Helper for Lemma 6.6: in dimension `1`, the identity map at the concrete direction
`e₀` has the expected punctured directional limit, while the unpunctured target-limit claim
still fails. -/
lemma helperForLemma_6_6_finOne_identity_punctured_limit_and_unpunctured_failure :
    ∃ x₀ v : EuclideanSpace ℝ (Fin 1),
      Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin 1) => x) (x₀ + t • v) -
            (fun x : EuclideanSpace ℝ (Fin 1) => x) x₀))
        (𝓝[≠] (0 : ℝ))
        (𝓝 v) ∧
      ¬ Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin 1) => x) (x₀ + t • v) -
            (fun x : EuclideanSpace ℝ (Fin 1) => x) x₀))
        (nhdsWithin (0 : ℝ)
          {t : ℝ | x₀ + t • v ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 1)))})
        (𝓝 v) := by
  let e0 : EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
  refine ⟨(0 : EuclideanSpace ℝ (Fin 1)), e0, ?_⟩
  have he0_ne : e0 ≠ 0 := by
    simpa [e0] using helperForLemma_6_6_standardBasisVector_finOne_ne_zero
  constructor
  · simpa [e0] using
      (helperForLemma_6_6_identity_punctured_directional_limit
        (x₀ := (0 : EuclideanSpace ℝ (Fin 1)))
        (v := e0))
  · simpa [e0] using
      (helperForLemma_6_6_unpunctured_identity_limit_impossible
        (x₀ := (0 : EuclideanSpace ℝ (Fin 1)))
        (v := e0)
        he0_ne)

/-- Helper for Lemma 6.6: for the identity map on `univ`, any unpunctured directional limit at
`0` forces the direction vector to be `0`. -/
lemma helperForLemma_6_6_identity_unpunctured_limit_forces_direction_zero
    {n : ℕ}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    (hlim : Filter.Tendsto
      (fun t : ℝ =>
        t⁻¹ • ((fun x : EuclideanSpace ℝ (Fin n) => x) (x₀ + t • v) -
          (fun x : EuclideanSpace ℝ (Fin n) => x) x₀))
      (nhdsWithin (0 : ℝ)
        {t : ℝ | x₀ + t • v ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))})
      (𝓝 ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v))) :
    v = 0 := by
  have hx₀ : x₀ ∈ interior (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [interior_univ]
  have hzero : ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v) = 0 :=
    helperForLemma_6_6_unpunctured_limit_forces_zero
      (E := (Set.univ : Set (EuclideanSpace ℝ (Fin n))))
      (f := fun x : EuclideanSpace ℝ (Fin n) => x)
      (x₀ := x₀)
      (v := v)
      (f' := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      hx₀
      hlim
  simpa using hzero

/-- Helper for Lemma 6.6: interior-point differentiability within `E` upgrades to ambient
Fréchet differentiability at the same base point. -/
lemma helperForLemma_6_6_hasFDerivAt_of_hasFDerivWithinAt_interior
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hfd : HasFDerivWithinAt f f' E x₀) :
    HasFDerivAt f f' x₀ := by
  have hE_nhds : E ∈ 𝓝 x₀ :=
    Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hx₀) interior_subset
  exact hfd.hasFDerivAt hE_nhds

/-- Helper for Lemma 6.6: an ambient Fréchet derivative yields the punctured directional
difference-quotient limit along `𝓝[≠] 0`. -/
lemma helperForLemma_6_6_tendsto_directionalQuotient_on_punctured_nhds
    {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfdAt : HasFDerivAt f f' x₀) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (f' v)) := by
  have hline : HasLineDerivAt ℝ f (f' v) x₀ v :=
    hfdAt.hasLineDerivAt v
  simpa using hline.tendsto_slope_zero

/-- Helper for Lemma 6.6: a punctured-neighborhood directional limit remains valid after
restricting the source filter to points with `x₀ + t • v ∈ E`. -/
lemma helperForLemma_6_6_mono_to_constrainted_punctured_filter
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hpunctured : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (f' v))) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  have hsubset :
      {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E} ⊆ {t : ℝ | t ≠ 0} := by
    intro t ht
    exact ht.1
  exact hpunctured.mono_left (nhdsWithin_mono (0 : ℝ) hsubset)

/-- Helper for Lemma 6.6: the punctured directional-quotient formulation is derivable from a
within-domain Fréchet derivative at an interior point. -/
lemma helperForLemma_6_6_punctured_directional_limit_of_hasFDerivWithinAt
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hfd : HasFDerivWithinAt f f' E x₀) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  have hfdAt : HasFDerivAt f f' x₀ :=
    helperForLemma_6_6_hasFDerivAt_of_hasFDerivWithinAt_interior
      (x₀ := x₀)
      (f' := f')
      hx₀
      hfd
  have hpunctured :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (f' v)) :=
    helperForLemma_6_6_tendsto_directionalQuotient_on_punctured_nhds
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hfdAt
  exact helperForLemma_6_6_mono_to_constrainted_punctured_filter
    (E := E)
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hpunctured

/-- Helper for Lemma 6.6: differentiability at an interior point yields the punctured
directional-difference-quotient limit to `f' v`, i.e. the mathematically correct directional
limit statement with `t ≠ 0` explicitly enforced in the source filter. -/
lemma helperForLemma_6_6_hasDirectionalDerivWithinAt_eq_fderiv_punctured
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hfd : HasFDerivWithinAt f f' E x₀) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  exact helperForLemma_6_6_punctured_directional_limit_of_hasFDerivWithinAt
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    hfd

/-- Helper for Lemma 6.6: corrected directional-derivative statement using the punctured
source filter (`t ≠ 0`), matching the mathematically valid formulation. -/
lemma helperForLemma_6_6_hasDirectionalDerivWithinAt_eq_fderiv_corrected
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hfd : HasFDerivWithinAt f f' E x₀) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  exact helperForLemma_6_6_hasDirectionalDerivWithinAt_eq_fderiv_punctured
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    hfd

/-- Helper for Lemma 6.6: if the theorem's unpunctured directional-limit claim holds for given
data, then the directional value `f' v` is forced to be zero. -/
lemma helperForLemma_6_6_target_claim_forces_zero
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hclaim : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) :
    f' v = 0 := by
  exact helperForLemma_6_6_unpunctured_limit_forces_zero
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    hclaim

/-- Helper for Lemma 6.6: at an interior point, any unpunctured directional-limit claim with
nonzero directional value is contradictory; this obstruction does not use differentiability. -/
lemma helperForLemma_6_6_nonzero_directionalValue_precludes_unpunctured_target
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hv0 : f' v ≠ 0) :
    ¬ Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  intro htarget
  exact hv0 (helperForLemma_6_6_target_claim_forces_zero
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    htarget)

/-- Helper for Lemma 6.6: at an interior point, the unpunctured directional-constraint set
is obtained by inserting `0` into the punctured constraint set. -/
lemma helperForLemma_6_6_directionConstraint_eq_insert_zero_punctured
    {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E) :
    {t : ℝ | x₀ + t • v ∈ E} =
      insert (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E} := by
  have hzeroMem : (0 : ℝ) ∈ {t : ℝ | x₀ + t • v ∈ E} :=
    helperForLemma_6_6_zero_mem_directionConstraint (x₀ := x₀) (v := v) hx₀
  ext t
  by_cases ht : t = 0
  · subst ht
    simp [hzeroMem]
  · constructor
    · intro htE
      exact Or.inr ⟨ht, htE⟩
    · intro htInsert
      rcases htInsert with ht0 | htE
      · exact (ht ht0).elim
      · exact htE.2

/-- Helper for Lemma 6.6: if the punctured directional quotient tends to `f' v` and that value
is `0`, then the corresponding unpunctured directional limit follows. -/
lemma helperForLemma_6_6_unpunctured_limit_of_punctured_limit_and_zero_directional_value
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hpunctured : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (f' v)))
    (hv0 : f' v = 0) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  have hset :
      {t : ℝ | x₀ + t • v ∈ E} =
        insert (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E} :=
    helperForLemma_6_6_directionConstraint_eq_insert_zero_punctured
      (x₀ := x₀)
      (v := v)
      hx₀
  have hvalueAtZero :
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) 0 = f' v := by
    calc
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) 0 = 0 :=
        helperForLemma_6_6_differenceQuotient_valueAtZero (f := f) (x₀ := x₀) (v := v)
      _ = f' v := by simpa [hv0]
  have hpure :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (pure (0 : ℝ))
        (𝓝 (f' v)) := by
    have hpureAtValue :
        Filter.Tendsto
          (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
          (pure (0 : ℝ))
          (𝓝 ((fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) 0)) :=
      tendsto_pure_nhds (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) 0
    exact hvalueAtZero ▸ hpureAtValue
  have hsup :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (pure (0 : ℝ) ⊔ nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
        (𝓝 (f' v)) :=
    hpure.sup hpunctured
  have hinsert :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) (insert (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E}))
        (𝓝 (f' v)) := by
    simpa [nhdsWithin_insert] using hsup
  simpa [hset] using hinsert

/-- Helper for Lemma 6.6: once the punctured directional quotient converges to `f' v`,
the unpunctured directional-limit claim is equivalent to the vanishing condition `f' v = 0`. -/
lemma helperForLemma_6_6_unpunctured_limit_iff_zero_of_punctured_limit
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ interior E)
    (hpunctured : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (f' v))) :
    (Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) ↔
      f' v = 0 := by
  constructor
  · intro hunpunctured
    exact helperForLemma_6_6_unpunctured_limit_forces_zero
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hunpunctured
  · intro hv0
    exact helperForLemma_6_6_unpunctured_limit_of_punctured_limit_and_zero_directional_value
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hpunctured
      hv0

/-- Helper for Lemma 6.6: there exists explicit differentiable data (identity map on `univ` in
dimension `1`) for which the theorem's unpunctured directional-limit conclusion fails. -/
lemma helperForLemma_6_6_explicit_unpunctured_counterexample_data :
    ∃ (E : Set (EuclideanSpace ℝ (Fin 1)))
      (f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
      (x₀ v : EuclideanSpace ℝ (Fin 1))
      (f' : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)),
      x₀ ∈ interior E ∧
      HasFDerivWithinAt f f' E x₀ ∧
      ¬ Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v)) := by
  let e0 : EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
  refine ⟨(Set.univ : Set (EuclideanSpace ℝ (Fin 1))),
    (fun x : EuclideanSpace ℝ (Fin 1) => x),
    (0 : EuclideanSpace ℝ (Fin 1)),
    e0,
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))),
    ?_⟩
  constructor
  · simpa [interior_univ]
  constructor
  · exact
      helperForLemma_6_6_id_hasFDerivWithinAt_univ
        (x₀ := (0 : EuclideanSpace ℝ (Fin 1)))
  · have he0_ne : e0 ≠ 0 := by
      simpa [e0] using helperForLemma_6_6_standardBasisVector_finOne_ne_zero
    simpa [e0] using
      (helperForLemma_6_6_unpunctured_identity_limit_impossible
        (x₀ := (0 : EuclideanSpace ℝ (Fin 1)))
        (v := e0)
        he0_ne)

/-- Helper for Lemma 6.6: there is explicit differentiable data (identity map on `univ` in
dimension `1`) where the unpunctured directional-limit conclusion fails and the claimed limit
value `f' v` is nonzero. -/
lemma helperForLemma_6_6_explicit_unpunctured_counterexample_data_with_nonzero_value :
    ∃ (E : Set (EuclideanSpace ℝ (Fin 1)))
      (f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
      (x₀ v : EuclideanSpace ℝ (Fin 1))
      (f' : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)),
      x₀ ∈ interior E ∧
      HasFDerivWithinAt f f' E x₀ ∧
      f' v ≠ 0 ∧
      ¬ Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v)) := by
  let e0 : EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
  refine ⟨(Set.univ : Set (EuclideanSpace ℝ (Fin 1))),
    (fun x : EuclideanSpace ℝ (Fin 1) => x),
    (0 : EuclideanSpace ℝ (Fin 1)),
    e0,
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))),
    ?_⟩
  have he0_ne : e0 ≠ 0 := by
    simpa [e0] using helperForLemma_6_6_standardBasisVector_finOne_ne_zero
  have hderiv :
      HasFDerivWithinAt
        (fun x : EuclideanSpace ℝ (Fin 1) => x)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))
        (Set.univ : Set (EuclideanSpace ℝ (Fin 1)))
        (0 : EuclideanSpace ℝ (Fin 1)) :=
    helperForLemma_6_6_id_hasFDerivWithinAt_univ
      (x₀ := (0 : EuclideanSpace ℝ (Fin 1)))
  have hnonzeroValue :
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) e0 ≠ 0 := by
    simpa using he0_ne
  have hnot :
      ¬ Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            ((fun x : EuclideanSpace ℝ (Fin 1) => x)
              ((0 : EuclideanSpace ℝ (Fin 1)) + t • e0) -
              (fun x : EuclideanSpace ℝ (Fin 1) => x) (0 : EuclideanSpace ℝ (Fin 1))))
        (nhdsWithin (0 : ℝ)
          {t : ℝ |
            (0 : EuclideanSpace ℝ (Fin 1)) + t • e0 ∈
              (Set.univ : Set (EuclideanSpace ℝ (Fin 1)))})
        (𝓝 ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) e0)) :=
    helperForLemma_6_6_unpunctured_identity_limit_impossible
      (x₀ := (0 : EuclideanSpace ℝ (Fin 1)))
      (v := e0)
      he0_ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [interior_univ]
  · exact hderiv
  · exact hnonzeroValue
  · simpa [e0] using hnot

/-- Helper for Lemma 6.6: the unpunctured directional-limit conclusion cannot hold as a
universal theorem; the explicit dimension-`1` identity-map data is a counterexample. -/
lemma helperForLemma_6_6_unpunctured_universal_claim_false :
    ¬ (∀ {n m : ℕ}
      {E : Set (EuclideanSpace ℝ (Fin n))}
      {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
      {x₀ : EuclideanSpace ℝ (Fin n)}
      (hx₀ : x₀ ∈ interior E)
      {v : EuclideanSpace ℝ (Fin n)}
      {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)},
      HasFDerivWithinAt f f' E x₀ →
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) := by
  intro hforall
  rcases helperForLemma_6_6_explicit_unpunctured_counterexample_data with
    ⟨E, f, x₀, v, f', hx₀, hfd, hnot⟩
  have hlim :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v)) :=
    hforall (n := 1) (m := 1) (E := E) (f := f) (x₀ := x₀) hx₀ (v := v) (f' := f') hfd
  exact hnot hlim

/-- Helper for Lemma 6.6: even after restricting to nonzero directional values `f' v ≠ 0`,
the unpunctured directional-limit conclusion is still not universally valid. -/
lemma helperForLemma_6_6_unpunctured_nonzero_directional_universal_claim_false :
    ¬ (∀ {n m : ℕ}
      {E : Set (EuclideanSpace ℝ (Fin n))}
      {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
      {x₀ : EuclideanSpace ℝ (Fin n)}
      (hx₀ : x₀ ∈ interior E)
      {v : EuclideanSpace ℝ (Fin n)}
      {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)},
      HasFDerivWithinAt f f' E x₀ →
      f' v ≠ 0 →
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) := by
  intro hforall
  rcases helperForLemma_6_6_explicit_unpunctured_counterexample_data_with_nonzero_value with
    ⟨E, f, x₀, v, f', hx₀, hfd, hv0, hnot⟩
  have hlim :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v)) :=
    hforall (n := 1) (m := 1) (E := E) (f := f) (x₀ := x₀) hx₀ (v := v) (f' := f') hfd hv0
  exact hnot hlim

/-- Helper for Lemma 6.6: for fixed differentiable data, the theorem's unpunctured
directional-limit claim is equivalent to the directional value `f' v` being zero. -/
lemma helperForLemma_6_6_target_tendsto_iff_directionalValue_eq_zero
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀) :
    (Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) ↔
      f' v = 0 := by
  constructor
  · intro htarget
    exact helperForLemma_6_6_target_claim_forces_zero
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      htarget
  · intro hv0
    have hpunctured :
        Filter.Tendsto
          (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
          (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
          (𝓝 (f' v)) :=
      helperForLemma_6_6_punctured_directional_limit_of_hasFDerivWithinAt
        (x₀ := x₀)
        (v := v)
        (hx₀ := hx₀)
        (hfd := hfd)
    exact
      helperForLemma_6_6_unpunctured_limit_of_punctured_limit_and_zero_directional_value
        (x₀ := x₀)
        (v := v)
        (f' := f')
        hx₀
        hpunctured
        hv0

/-- Helper for Lemma 6.6: if the directional value `f' v` is nonzero, then the theorem's
unpunctured directional-limit claim is impossible for that fixed differentiable data. -/
lemma helperForLemma_6_6_not_target_tendsto_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0) :
    ¬ Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  intro htarget
  have htargetIffZero :
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) ↔
        f' v = 0 :=
    helperForLemma_6_6_target_tendsto_iff_directionalValue_eq_zero
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd
  exact hv0 (htargetIffZero.mp htarget)

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, failure of the
unpunctured directional-limit target is equivalent to the directional value being nonzero. -/
lemma helperForLemma_6_6_not_target_tendsto_iff_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀) :
    (¬ Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) ↔
      f' v ≠ 0 := by
  constructor
  · intro hnot
    intro hzero
    exact hnot
      ((helperForLemma_6_6_target_tendsto_iff_directionalValue_eq_zero
        (x₀ := x₀)
        (v := v)
        (f' := f')
        hx₀
        hfd).2 hzero)
  · intro hv0
    exact
      helperForLemma_6_6_not_target_tendsto_of_nonzero_directionalValue
        (x₀ := x₀)
        (v := v)
        (f' := f')
        hx₀
        hfd
        hv0

/-- Helper for Lemma 6.6: if the theorem's unpunctured directional-limit conclusion held for
every direction (for fixed data at an interior point), then the derivative map would be the
zero linear map. -/
lemma helperForLemma_6_6_all_unpunctured_targets_force_zero_fderiv
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hall : ∀ w : EuclideanSpace ℝ (Fin n),
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • w) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • w ∈ E})
        (𝓝 (f' w))) :
    f' = 0 := by
  ext w i
  exact congrArg (fun z : EuclideanSpace ℝ (Fin m) => z i)
    (helperForLemma_6_6_target_claim_forces_zero
      (x₀ := x₀)
      (v := w)
      (f' := f')
      hx₀
      (hall w))

/-- Helper for Lemma 6.6: for fixed differentiable data, any proof of the theorem's
unpunctured directional-limit target contradicts a nonzero directional value `f' v`. -/
lemma helperForLemma_6_6_target_proof_contradicts_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0)
    (htarget : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) :
    False := by
  exact
    (helperForLemma_6_6_not_target_tendsto_of_nonzero_directionalValue
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd
      hv0) htarget

/-- Helper for Lemma 6.6: if the theorem's target claim is equivalent to the vanishing
directional value `f' v = 0`, then any nonzero directional value excludes that target claim. -/
lemma helperForLemma_6_6_not_target_of_targetIff_directionalValue_eq_zero
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (htargetIffZero :
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) ↔
        f' v = 0)
    (hv0 : f' v ≠ 0) :
    ¬ Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  intro htarget
  exact hv0 (htargetIffZero.mp htarget)

/-- Helper for Lemma 6.6: if the theorem's target claim is equivalent to `f' v = 0`, then
under `f' v ≠ 0` that target claim is equivalent to `False`. -/
lemma helperForLemma_6_6_targetIffFalse_of_targetIffZero_and_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (htargetIffZero :
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) ↔
        f' v = 0)
    (hv0 : f' v ≠ 0) :
    (Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) ↔
      False := by
  constructor
  · intro htarget
    exact hv0 (htargetIffZero.mp htarget)
  · intro hfalse
    exact False.elim hfalse

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, if
`f' v ≠ 0`, then the theorem's unpunctured target statement is equivalent to `False`. -/
lemma helperForLemma_6_6_targetIffFalse_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0) :
    (Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) ↔
      False := by
  exact helperForLemma_6_6_targetIffFalse_of_targetIffZero_and_nonzero_directionalValue
    (x₀ := x₀)
    (v := v)
    (f' := f')
    (helperForLemma_6_6_target_tendsto_iff_directionalValue_eq_zero
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd)
    hv0


end Section03
end Chap06
