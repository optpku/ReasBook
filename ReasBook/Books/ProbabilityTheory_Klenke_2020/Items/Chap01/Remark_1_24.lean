/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_23

open MeasureTheory MeasurableSpace Set

/-- Helper for Remark 1.24: once a Euclidean generator family is a `π`-system, Dynkin's
`π`-`λ` theorem upgrades Theorem 1.23 to the corresponding equality of Dynkin systems. -/
private lemma dynkin_eq_of_borel_eq_generateFrom_euclideanBorelGeneratorClass
    {n : ℕ} {i : EuclideanBorelGenerator}
    (hpi : IsPiSystem (euclideanBorelGeneratorClass n i)) :
    DynkinSystem.ofMeasurableSpace (borel (Fin n → ℝ)) =
      DynkinSystem.generate (euclideanBorelGeneratorClass n i) := by
  simpa [borel_eq_generateFrom_euclideanBorelGeneratorClass n i,
    DynkinSystem.ofMeasurableSpace_toMeasurableSpace] using
    congrArg DynkinSystem.ofMeasurableSpace (DynkinSystem.generateFrom_eq hpi)

/-- Helper for Remark 1.24: the nested-union presentation of rational open intervals agrees with
the direct existential set-builder presentation. -/
private lemma rational_Ioo_family :
    (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioo (a : ℝ) (b : ℝ)} : Set (Set ℝ))) =
      {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo (a : ℝ) (b : ℝ)} := by
  ext S
  simp

/-- Helper for Remark 1.24: the nested-union presentation of rational `(a, b]` intervals agrees
with the direct existential set-builder presentation. -/
private lemma rational_Ioc_family :
    (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioc (a : ℝ) (b : ℝ)} : Set (Set ℝ))) =
      {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioc (a : ℝ) (b : ℝ)} := by
  ext S
  simp

/-- Helper for Remark 1.24: the nested-union presentation of rational `[a, b)` intervals agrees
with the direct existential set-builder presentation. -/
private lemma rational_Ico_family :
    (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ico (a : ℝ) (b : ℝ)} : Set (Set ℝ))) =
      {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ico (a : ℝ) (b : ℝ)} := by
  ext S
  simp

/-- Helper for Remark 1.24: the nested-union presentation of rational closed intervals agrees
with the direct existential set-builder presentation. -/
private lemma rational_Icc_family :
    (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a ≤ b), ({Icc (a : ℝ) (b : ℝ)} : Set (Set ℝ))) =
      {S : Set ℝ | ∃ a b : ℚ, a ≤ b ∧ S = Icc (a : ℝ) (b : ℝ)} := by
  ext S
  simp

/-- Helper for Remark 1.24: the rational lower-open orthant generator is a `π`-system. -/
private lemma isPiSystem_rationalOpenLowerOrthants (n : ℕ) :
    IsPiSystem (euclideanBorelGeneratorClass n .rationalOpenLowerOrthants) := by
  have hfamily :
      euclideanBorelGeneratorClass n .rationalOpenLowerOrthants =
        Set.pi univ '' Set.pi univ (fun _ : Fin n ↦ ⋃ q : ℚ, ({Iio (q : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_single_endpoint_generator_eq_pi n (fun q ↦ Iio (q : ℝ))
  rw [hfamily]
  exact IsPiSystem.pi fun _ ↦ Real.isPiSystem_Iio_rat

/-- Helper for Remark 1.24: the rational lower-closed orthant generator is a `π`-system. -/
private lemma isPiSystem_rationalClosedLowerOrthants (n : ℕ) :
    IsPiSystem (euclideanBorelGeneratorClass n .rationalClosedLowerOrthants) := by
  have hfamily :
      euclideanBorelGeneratorClass n .rationalClosedLowerOrthants =
        Set.pi univ '' Set.pi univ (fun _ : Fin n ↦ ⋃ q : ℚ, ({Iic (q : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_single_endpoint_generator_eq_pi n (fun q ↦ Iic (q : ℝ))
  rw [hfamily]
  exact IsPiSystem.pi fun _ ↦ Real.isPiSystem_Iic_rat

/-- Helper for Remark 1.24: the rational upper-open orthant generator is a `π`-system. -/
private lemma isPiSystem_rationalOpenUpperOrthants (n : ℕ) :
    IsPiSystem (euclideanBorelGeneratorClass n .rationalOpenUpperOrthants) := by
  have hfamily :
      euclideanBorelGeneratorClass n .rationalOpenUpperOrthants =
        Set.pi univ '' Set.pi univ (fun _ : Fin n ↦ ⋃ q : ℚ, ({Ioi (q : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_single_endpoint_generator_eq_pi n (fun q ↦ Ioi (q : ℝ))
  rw [hfamily]
  exact IsPiSystem.pi fun _ ↦ Real.isPiSystem_Ioi_rat

/-- Helper for Remark 1.24: the rational upper-closed orthant generator is a `π`-system. -/
private lemma isPiSystem_rationalClosedUpperOrthants (n : ℕ) :
    IsPiSystem (euclideanBorelGeneratorClass n .rationalClosedUpperOrthants) := by
  have hfamily :
      euclideanBorelGeneratorClass n .rationalClosedUpperOrthants =
        Set.pi univ '' Set.pi univ (fun _ : Fin n ↦ ⋃ q : ℚ, ({Ici (q : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_single_endpoint_generator_eq_pi n (fun q ↦ Ici (q : ℝ))
  rw [hfamily]
  exact IsPiSystem.pi fun _ ↦ Real.isPiSystem_Ici_rat

/-- Helper for Remark 1.24: the rational open-rectangle generator is a `π`-system. -/
private lemma isPiSystem_rationalOpenRectangles (n : ℕ) :
    IsPiSystem (euclideanBorelGeneratorClass n .rationalOpenRectangles) := by
  have hfamily :
      euclideanBorelGeneratorClass n .rationalOpenRectangles =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n ↦
            ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioo (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_two_endpoint_generator_eq_pi n (fun a b ↦ Ioo (a : ℝ) (b : ℝ))
  rw [hfamily]
  refine IsPiSystem.pi fun _ ↦ ?_
  rw [rational_Ioo_family]
  simpa [eq_comm] using isPiSystem_Ioo ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)

/-- Helper for Remark 1.24: the rational left-open right-closed rectangle generator is a
`π`-system. -/
private lemma isPiSystem_rationalLeftOpenRightClosedRectangles (n : ℕ) :
    IsPiSystem (euclideanBorelGeneratorClass n .rationalLeftOpenRightClosedRectangles) := by
  have hfamily :
      euclideanBorelGeneratorClass n .rationalLeftOpenRightClosedRectangles =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n ↦
            ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioc (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_two_endpoint_generator_eq_pi n (fun a b ↦ Ioc (a : ℝ) (b : ℝ))
  rw [hfamily]
  refine IsPiSystem.pi fun _ ↦ ?_
  rw [rational_Ioc_family]
  simpa [eq_comm] using isPiSystem_Ioc ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)

/-- Helper for Remark 1.24: the rational left-closed right-open rectangle generator is a
`π`-system. -/
private lemma isPiSystem_rationalLeftClosedRightOpenRectangles (n : ℕ) :
    IsPiSystem (euclideanBorelGeneratorClass n .rationalLeftClosedRightOpenRectangles) := by
  have hfamily :
      euclideanBorelGeneratorClass n .rationalLeftClosedRightOpenRectangles =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n ↦
            ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ico (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_two_endpoint_generator_eq_pi n (fun a b ↦ Ico (a : ℝ) (b : ℝ))
  rw [hfamily]
  refine IsPiSystem.pi fun _ ↦ ?_
  rw [rational_Ico_family]
  simpa [eq_comm] using isPiSystem_Ico ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)

/-- Helper for Remark 1.24: the rational closed-rectangle generator is a `π`-system once the
closed-rectangle case is stated with weak endpoint inequalities. -/
private lemma isPiSystem_rationalClosedRectangles (n : ℕ) :
    IsPiSystem (euclideanBorelGeneratorClass n .rationalClosedRectangles) := by
  have hfamily :
      euclideanBorelGeneratorClass n .rationalClosedRectangles =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n ↦
            ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a ≤ b), ({Icc (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_two_endpoint_generator_eq_pi_le n (fun a b ↦ Icc (a : ℝ) (b : ℝ))
  rw [hfamily]
  refine IsPiSystem.pi fun _ ↦ ?_
  rw [rational_Icc_family]
  simpa [eq_comm] using isPiSystem_Icc ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)

/-- Helper for Remark 1.24: all Euclidean generator families except the rational open balls are
`π`-systems. -/
private lemma isPiSystem_euclideanBorelGeneratorClass (n : ℕ) :
    ∀ i : EuclideanBorelGenerator, i ≠ .rationalOpenBalls →
      IsPiSystem (euclideanBorelGeneratorClass n i)
  | .openSets, _ => by simpa [euclideanBorelGeneratorClass] using isPiSystem_isOpen
  | .closedSets, _ => by simpa [euclideanBorelGeneratorClass] using isPiSystem_isClosed
  | .compactSets, _ => by
      intro s hs t ht hst
      simpa [euclideanBorelGeneratorClass] using hs.inter ht
  | .rationalOpenBalls, hi => (hi rfl).elim
  | .rationalOpenRectangles, _ => isPiSystem_rationalOpenRectangles n
  | .rationalClosedRectangles, _ => isPiSystem_rationalClosedRectangles n
  | .rationalLeftOpenRightClosedRectangles, _ =>
      isPiSystem_rationalLeftOpenRightClosedRectangles n
  | .rationalLeftClosedRightOpenRectangles, _ =>
      isPiSystem_rationalLeftClosedRightOpenRectangles n
  | .rationalOpenLowerOrthants, _ => isPiSystem_rationalOpenLowerOrthants n
  | .rationalClosedLowerOrthants, _ => isPiSystem_rationalClosedLowerOrthants n
  | .rationalOpenUpperOrthants, _ => isPiSystem_rationalOpenUpperOrthants n
  | .rationalClosedUpperOrthants, _ => isPiSystem_rationalClosedUpperOrthants n

/-- Helper for Remark 1.24: the one-parameter rational generator families are countable. -/
private lemma countable_single_parameter_family {α β : Type*} [Countable α] (f : α → Set β) :
    {s : Set β | ∃ a, s = f a}.Countable := by
  simpa [Set.range, eq_comm] using Set.countable_range f

-- Proof sketch: choose two distinct rational centers on a nontrivial coordinate axis and equal
-- rational radii so that the two balls overlap without one containing the other; their
-- intersection is not itself a Euclidean open ball, so it cannot stay in `\mathcal E_4`.
set_option maxHeartbeats 600000
/-- Remark 1.24: in dimension at least `2`, the rational open-ball generator `\mathcal E_4`
is not a `π`-system. -/
theorem euclideanBorelGeneratorClass_rationalOpenBalls_not_isPiSystem {n : ℕ}
    (hn : 1 < n) :
    ¬ IsPiSystem (euclideanBorelGeneratorClass n .rationalOpenBalls) := by
  let i0 : Fin n := ⟨0, lt_trans (by decide) hn⟩
  let i1 : Fin n := ⟨1, hn⟩
  have hi1_ne_i0 : i1 ≠ i0 := by
    intro h
    have : (1 : ℕ) = 0 := by
      simpa [i0, i1] using congrArg Fin.val h
    norm_num at this
  have hi0_ne_i1 : i0 ≠ i1 := fun h ↦ hi1_ne_i0 h.symm
  let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) := eL.toHomeomorph
  let z : EuclideanSpace ℝ (Fin n) :=
    eL.symm (fun j ↦ if j = i0 then (0 : ℝ) else if j = i1 then 0 else 0)
  let u : EuclideanSpace ℝ (Fin n) :=
    eL.symm (fun j ↦ if j = i0 then (1 : ℝ) else if j = i1 then 0 else 0)
  let p : EuclideanSpace ℝ (Fin n) :=
    eL.symm (fun j ↦ if j = i0 then (1 / 2 : ℝ) else if j = i1 then 0 else 0)
  let q : EuclideanSpace ℝ (Fin n) :=
    eL.symm (fun j ↦ if j = i0 then (1 / 2 : ℝ) else if j = i1 then (3 / 4 : ℝ) else 0)
  let q' : EuclideanSpace ℝ (Fin n) :=
    eL.symm (fun j ↦ if j = i0 then (1 / 2 : ℝ) else if j = i1 then (-3 / 4 : ℝ) else 0)
  have dist_sq_two_coords (a0 a1 b0 b1 : ℝ) :
      dist (eL.symm (fun j ↦ if j = i0 then a0 else if j = i1 then a1 else 0))
          (eL.symm (fun j ↦ if j = i0 then b0 else if j = i1 then b1 else 0)) ^ 2 =
        dist a0 b0 ^ 2 + dist a1 b1 ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hsum :
        ∑ j : Fin n,
          dist ((eL.symm (fun k ↦ if k = i0 then a0 else if k = i1 then a1 else 0)) j)
            ((eL.symm (fun k ↦ if k = i0 then b0 else if k = i1 then b1 else 0)) j) ^ 2 =
          ∑ j : Fin n,
            (if j = i0 then dist a0 b0 ^ 2 else if j = i1 then dist a1 b1 ^ 2 else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      by_cases hj0 : j = i0
      · subst hj0
        simp [eL]
      · by_cases hj1 : j = i1
        · subst hj1
          simp [eL, hi1_ne_i0]
        · simp [eL, hj0, hj1]
    rw [hsum]
    have hsubset : ({i0, i1} : Finset (Fin n)) ⊆ Finset.univ := by
      intro j hj
      simp
    have hzero :
        ∀ j ∈ Finset.univ,
          j ∉ ({i0, i1} : Finset (Fin n)) →
            (if j = i0 then dist a0 b0 ^ 2 else if j = i1 then dist a1 b1 ^ 2 else 0) = 0 := by
      intro j hj hjnot
      simp at hjnot
      simp [hjnot.1, hjnot.2]
    have hsupport :
        (∑ j ∈ ({i0, i1} : Finset (Fin n)),
            if j = i0 then dist a0 b0 ^ 2 else if j = i1 then dist a1 b1 ^ 2 else 0) =
          ∑ j : Fin n,
            if j = i0 then dist a0 b0 ^ 2 else if j = i1 then dist a1 b1 ^ 2 else 0 := by
      simpa using Finset.sum_subset hsubset hzero
    rw [← hsupport, Finset.sum_pair hi0_ne_i1]
    simp [hi1_ne_i0]
  have hzu_formula (c : EuclideanSpace ℝ (Fin n)) :
      dist c z ^ 2 + dist c u ^ 2 = 2 * dist c p ^ 2 + 1 / 2 := by
    have hpoint :
        ∀ j : Fin n,
          dist (c j) 0 ^ 2 + dist (c j) (if j = i0 then (1 : ℝ) else 0) ^ 2 =
            2 * dist (c j) (if j = i0 then (1 / 2 : ℝ) else 0) ^ 2 +
              (if j = i0 then (1 / 2 : ℝ) else 0) := by
      intro j
      by_cases hj : j = i0
      · subst hj
        norm_num [Real.dist_eq]
        ring_nf
      · norm_num [Real.dist_eq, hj]
        ring_nf
    calc
      dist c z ^ 2 + dist c u ^ 2
          = ∑ j : Fin n,
              (dist (c j) 0 ^ 2 + dist (c j) (if j = i0 then (1 : ℝ) else 0) ^ 2) := by
            rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, ← Finset.sum_add_distrib]
            simp [z, u, eL]
      _ = ∑ j : Fin n,
              (2 * dist (c j) (if j = i0 then (1 / 2 : ℝ) else 0) ^ 2 +
                (if j = i0 then (1 / 2 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hpoint j]
      _ = 2 * dist c p ^ 2 + 1 / 2 := by
            rw [EuclideanSpace.dist_sq_eq, Finset.mul_sum, Finset.sum_add_distrib]
            simp [p, eL]
  have hqq' (c : EuclideanSpace ℝ (Fin n)) :
      dist c q ^ 2 + dist c q' ^ 2 = 2 * dist c p ^ 2 + 9 / 8 := by
    have hpoint :
        ∀ j : Fin n,
          dist (c j) (if j = i0 then (1 / 2 : ℝ) else if j = i1 then (3 / 4 : ℝ) else 0) ^ 2 +
            dist (c j) (if j = i0 then (1 / 2 : ℝ) else if j = i1 then (-3 / 4 : ℝ) else 0) ^ 2 =
              2 * dist (c j) (if j = i0 then (1 / 2 : ℝ) else 0) ^ 2 +
                (if j = i1 then (9 / 8 : ℝ) else 0) := by
      intro j
      by_cases hj0 : j = i0
      · subst hj0
        simp [hi0_ne_i1]
        ring_nf
      · by_cases hj1 : j = i1
        · subst hj1
          norm_num [Real.dist_eq, hi1_ne_i0]
          ring_nf
        · norm_num [Real.dist_eq, hj0, hj1]
          ring_nf
    calc
      dist c q ^ 2 + dist c q' ^ 2
          = ∑ j : Fin n,
              (dist (c j) (if j = i0 then (1 / 2 : ℝ) else if j = i1 then (3 / 4 : ℝ) else 0) ^ 2 +
                dist (c j) (if j = i0 then (1 / 2 : ℝ) else if j = i1 then (-3 / 4 : ℝ) else 0) ^ 2) := by
            rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, ← Finset.sum_add_distrib]
            simp [q, q', eL]
      _ = ∑ j : Fin n,
              (2 * dist (c j) (if j = i0 then (1 / 2 : ℝ) else 0) ^ 2 +
                (if j = i1 then (9 / 8 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hpoint j]
      _ = 2 * dist c p ^ 2 + 9 / 8 := by
            rw [EuclideanSpace.dist_sq_eq, Finset.mul_sum, Finset.sum_add_distrib]
            simp [p, eL]
  let s : Set (Fin n → ℝ) := e '' Metric.ball z 1
  let t : Set (Fin n → ℝ) := e '' Metric.ball u 1
  have hs : s ∈ euclideanBorelGeneratorClass n .rationalOpenBalls := by
    refine ⟨fun j ↦ if j = i0 then (0 : ℚ) else if j = i1 then 0 else 0, 1, by norm_num, ?_⟩
    symm
    simp [s, z, e, eL]
  have ht : t ∈ euclideanBorelGeneratorClass n .rationalOpenBalls := by
    refine ⟨fun j ↦ if j = i0 then (1 : ℚ) else if j = i1 then 0 else 0, 1, by norm_num, ?_⟩
    have hu_fun :
        (fun j ↦ ((if j = i0 then (1 : ℚ) else if j = i1 then 0 else 0 : ℚ) : ℝ)) =
          fun j ↦ if j = i0 then (1 : ℝ) else 0 := by
      funext j
      by_cases hj0 : j = i0
      · subst hj0
        simp
      · simp [hj0]
    have hu_center :
        e.symm (fun j ↦ ((if j = i0 then (1 : ℚ) else if j = i1 then 0 else 0 : ℚ) : ℝ)) =
          eL.symm (fun j ↦ if j = i0 then (1 : ℝ) else 0) := by
      simpa [e, eL] using congrArg e.toEquiv.symm hu_fun
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      rw [hu_center]
      simpa [u, eL, hi0_ne_i1] using hy
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      rw [hu_center] at hy
      simpa [u, eL, hi0_ne_i1] using hy
  have hpz : dist p z ^ 2 = (1 / 4 : ℝ) := by
    have hpz' := dist_sq_two_coords (1 / 2) 0 0 0
    norm_num [Real.dist_eq, hi1_ne_i0] at hpz'
    simpa [p, z, eL] using hpz'
  have hpu : dist p u ^ 2 = (1 / 4 : ℝ) := by
    have hpu' := dist_sq_two_coords (1 / 2) 0 1 0
    norm_num [Real.dist_eq, hi1_ne_i0] at hpu'
    simpa [p, u, eL] using hpu'
  have hqz : dist q z ^ 2 = (13 / 16 : ℝ) := by
    have hqz' := dist_sq_two_coords (1 / 2) (3 / 4) 0 0
    norm_num [Real.dist_eq, hi1_ne_i0] at hqz'
    simpa [q, z, eL] using hqz'
  have hqu : dist q u ^ 2 = (13 / 16 : ℝ) := by
    have hqu' := dist_sq_two_coords (1 / 2) (3 / 4) 1 0
    norm_num [Real.dist_eq, hi1_ne_i0] at hqu'
    simpa [q, u, eL] using hqu'
  have hqz' : dist q' z ^ 2 = (13 / 16 : ℝ) := by
    have hqz'' := dist_sq_two_coords (1 / 2) (-3 / 4) 0 0
    norm_num [q', z, eL, Real.dist_eq, hi1_ne_i0] at hqz''
    simpa [q', z, eL, neg_div] using hqz''
  have hqu' : dist q' u ^ 2 = (13 / 16 : ℝ) := by
    have hqu'' := dist_sq_two_coords (1 / 2) (-3 / 4) 1 0
    norm_num [q', u, eL, Real.dist_eq, hi1_ne_i0] at hqu''
    simpa [q', u, eL, neg_div] using hqu''
  have hzu_eq : dist z u ^ 2 = (1 : ℝ) := by
    have hzu' := dist_sq_two_coords 0 0 1 0
    norm_num [Real.dist_eq, hi1_ne_i0] at hzu'
    simpa [z, u, eL] using hzu'
  have hp_s_ball : p ∈ Metric.ball z 1 := by
    rw [Metric.mem_ball]
    have hpz_nonneg : 0 ≤ dist p z := dist_nonneg
    nlinarith
  have hp_t_ball : p ∈ Metric.ball u 1 := by
    rw [Metric.mem_ball]
    have hpu_nonneg : 0 ≤ dist p u := dist_nonneg
    nlinarith
  have hq_s_ball : q ∈ Metric.ball z 1 := by
    rw [Metric.mem_ball]
    have hqz_nonneg : 0 ≤ dist q z := dist_nonneg
    nlinarith
  have hq_t_ball : q ∈ Metric.ball u 1 := by
    rw [Metric.mem_ball]
    have hqu_nonneg : 0 ≤ dist q u := dist_nonneg
    nlinarith
  have hq'_s_ball : q' ∈ Metric.ball z 1 := by
    rw [Metric.mem_ball]
    have hqz'_nonneg : 0 ≤ dist q' z := dist_nonneg
    nlinarith
  have hq'_t_ball : q' ∈ Metric.ball u 1 := by
    rw [Metric.mem_ball]
    have hqu'_nonneg : 0 ≤ dist q' u := dist_nonneg
    nlinarith
  have hz_t_ball : z ∉ Metric.ball u 1 := by
    rw [Metric.mem_ball]
    have hzu_nonneg : 0 ≤ dist z u := dist_nonneg
    nlinarith
  have hu_s_ball : u ∉ Metric.ball z 1 := by
    rw [Metric.mem_ball]
    have huz_nonneg : 0 ≤ dist u z := dist_nonneg
    have huz : dist u z ^ 2 = (1 : ℝ) := by simpa [dist_comm] using hzu_eq
    nlinarith
  have hp_s : e p ∈ s := by
    exact ⟨p, hp_s_ball, rfl⟩
  have hp_t : e p ∈ t := by
    exact ⟨p, hp_t_ball, rfl⟩
  have hq_s : e q ∈ s := by
    exact ⟨q, hq_s_ball, rfl⟩
  have hq_t : e q ∈ t := by
    exact ⟨q, hq_t_ball, rfl⟩
  have hq'_s : e q' ∈ s := by
    exact ⟨q', hq'_s_ball, rfl⟩
  have hq'_t : e q' ∈ t := by
    exact ⟨q', hq'_t_ball, rfl⟩
  intro hpi
  have hst : s ∩ t ∈ euclideanBorelGeneratorClass n .rationalOpenBalls :=
    hpi s hs t ht ⟨e p, hp_s, hp_t⟩
  rw [euclideanBorelGeneratorClass] at hst
  rcases hst with ⟨c, r, hr, hst⟩
  let center : EuclideanSpace ℝ (Fin n) := eL.symm (fun j ↦ (c j : ℝ))
  have hballs : Metric.ball z 1 ∩ Metric.ball u 1 = Metric.ball center (r : ℝ) := by
    have hs_pre : e ⁻¹' s = Metric.ball z 1 := by
      simp [s]
    have ht_pre : e ⁻¹' t = Metric.ball u 1 := by
      simp [t]
    have hpre := congrArg (fun A : Set (Fin n → ℝ) ↦ e ⁻¹' A) hst
    change e ⁻¹' (s ∩ t) = e ⁻¹' (e '' Metric.ball center (r : ℝ)) at hpre
    rw [Set.preimage_inter, hs_pre, ht_pre, e.preimage_image] at hpre
    simpa [center] using hpre
  have hp_ball : p ∈ Metric.ball center (r : ℝ) := by
    have hp_st : p ∈ Metric.ball z 1 ∩ Metric.ball u 1 := ⟨hp_s_ball, hp_t_ball⟩
    rw [hballs] at hp_st
    exact hp_st
  have hq_ball : q ∈ Metric.ball center (r : ℝ) := by
    have hq_st : q ∈ Metric.ball z 1 ∩ Metric.ball u 1 := ⟨hq_s_ball, hq_t_ball⟩
    rw [hballs] at hq_st
    exact hq_st
  have hq'_ball : q' ∈ Metric.ball center (r : ℝ) := by
    have hq'_st : q' ∈ Metric.ball z 1 ∩ Metric.ball u 1 := ⟨hq'_s_ball, hq'_t_ball⟩
    rw [hballs] at hq'_st
    exact hq'_st
  have hz_ball : z ∉ Metric.ball center (r : ℝ) := by
    intro hz_ball
    have hz_st : z ∈ Metric.ball z 1 ∩ Metric.ball u 1 := by
      rw [hballs]
      exact hz_ball
    exact hz_t_ball hz_st.2
  have hu_ball : u ∉ Metric.ball center (r : ℝ) := by
    intro hu_ball
    have hu_st : u ∈ Metric.ball z 1 ∩ Metric.ball u 1 := by
      rw [hballs]
      exact hu_ball
    exact hu_s_ball hu_st.1
  have hq_lt : dist center q < (r : ℝ) := by
    simpa [Metric.mem_ball, dist_comm] using hq_ball
  have hq'_lt : dist center q' < (r : ℝ) := by
    simpa [Metric.mem_ball, dist_comm] using hq'_ball
  have hz_ge : (r : ℝ) ≤ dist center z := by
    exact le_of_not_gt (by simpa [Metric.mem_ball, dist_comm] using hz_ball)
  have hu_ge : (r : ℝ) ≤ dist center u := by
    exact le_of_not_gt (by simpa [Metric.mem_ball, dist_comm] using hu_ball)
  have hq_sq : dist center q ^ 2 < (r : ℝ) ^ 2 := by
    have hq_nonneg : 0 ≤ dist center q := dist_nonneg
    nlinarith
  have hq'_sq : dist center q' ^ 2 < (r : ℝ) ^ 2 := by
    have hq'_nonneg : 0 ≤ dist center q' := dist_nonneg
    nlinarith
  have hupper : dist center q ^ 2 + dist center q' ^ 2 < 2 * (r : ℝ) ^ 2 := by
    have hsum : dist center q ^ 2 + dist center q' ^ 2 < (r : ℝ) ^ 2 + (r : ℝ) ^ 2 :=
      add_lt_add hq_sq hq'_sq
    simpa [two_mul] using hsum
  have hz_sq : (r : ℝ) ^ 2 ≤ dist center z ^ 2 := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast hr.le
    have hz_nonneg : 0 ≤ dist center z := dist_nonneg
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hr_nonneg, abs_of_nonneg hz_nonneg] using hz_ge)
  have hu_sq : (r : ℝ) ^ 2 ≤ dist center u ^ 2 := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast hr.le
    have hu_nonneg : 0 ≤ dist center u := dist_nonneg
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hr_nonneg, abs_of_nonneg hu_nonneg] using hu_ge)
  have hlower : 2 * (r : ℝ) ^ 2 ≤ dist center z ^ 2 + dist center u ^ 2 := by
    have hsum : (r : ℝ) ^ 2 + (r : ℝ) ^ 2 ≤ dist center z ^ 2 + dist center u ^ 2 :=
      add_le_add hz_sq hu_sq
    simpa [two_mul] using hsum
  rw [hqq' center] at hupper
  rw [hzu_formula center] at hlower
  nlinarith

-- Proof sketch: every generator family except the rational open balls is closed under finite
-- intersections by direct inspection of its defining formulas.
/-- Every Euclidean Borel generator except the rational open balls is a `π`-system. -/
private lemma euclideanBorelGeneratorClass_isPiSystem (n : ℕ) {i : EuclideanBorelGenerator}
    (hi : i ≠ .rationalOpenBalls) :
    IsPiSystem (euclideanBorelGeneratorClass n i) :=
  isPiSystem_euclideanBorelGeneratorClass n i hi

-- Proof sketch: combine the `π`-system statement with Theorem 1.23 and Dynkin's
-- `π`-`λ` theorem.
/-- For every Euclidean Borel generator except the rational open balls, the Dynkin system it
generates is the Borel `σ`-algebra on `ℝⁿ`. -/
private lemma euclideanBorelGeneratorClass_dynkin_eq (n : ℕ) {i : EuclideanBorelGenerator}
    (hi : i ≠ .rationalOpenBalls) :
    DynkinSystem.ofMeasurableSpace (borel (Fin n → ℝ)) =
      DynkinSystem.generate (euclideanBorelGeneratorClass n i) := by
  exact dynkin_eq_of_borel_eq_generateFrom_euclideanBorelGeneratorClass
    (euclideanBorelGeneratorClass_isPiSystem n hi)

-- Proof sketch: for each family other than the rational open balls, closure under finite
-- intersections is checked directly from the defining formulas, and then Theorem 1.23 together
-- with Dynkin's `π`-`λ` theorem identifies the generated `λ`-system with the Borel
-- `σ`-algebra.
/-- Remark 1.24: Every generating family `\mathcal E_i` with
`i = 1, 2, 3, 5, \ldots, 12` is a `π`-system, and for each such family the Borel
`σ`-algebra on `ℝⁿ` coincides with the generated `λ`-system. -/
theorem euclidean_borel_generators_piSystem_and_generatedLambdaFamily (n : ℕ) :
    ∀ i : EuclideanBorelGenerator,
      i ≠ .rationalOpenBalls →
        IsPiSystem (euclideanBorelGeneratorClass n i) ∧
          DynkinSystem.ofMeasurableSpace (borel (Fin n → ℝ)) =
            DynkinSystem.generate (euclideanBorelGeneratorClass n i) := by
  intro i hi
  exact ⟨euclideanBorelGeneratorClass_isPiSystem n hi,
    euclideanBorelGeneratorClass_dynkin_eq n hi⟩

/-- Remark 1.24: in dimension at least `2`, among the Euclidean Borel generators, exactly the
rational open balls fail to form a `π`-system. -/
theorem euclideanBorelGeneratorClass_isPiSystem_iff {n : ℕ} (hn : 1 < n)
    (i : EuclideanBorelGenerator) :
    IsPiSystem (euclideanBorelGeneratorClass n i) ↔ i ≠ .rationalOpenBalls := by
  constructor
  · intro hi hi4
    subst hi4
    exact euclideanBorelGeneratorClass_rationalOpenBalls_not_isPiSystem hn hi
  · intro hi
    exact euclideanBorelGeneratorClass_isPiSystem n hi

-- Proof sketch: each rational generator family is the image of a countable parameter space of
-- rational endpoints or rational centers and radii.
/-- The rational Euclidean Borel generators `\mathcal E_4, \ldots, \mathcal E_{12}` form
countable families of sets. -/
theorem euclidean_rational_borel_generators_countable (n : ℕ) {i : EuclideanBorelGenerator}
    (hi : i.IsRational) :
    (euclideanBorelGeneratorClass n i).Countable := by
  cases i with
  | openSets => exact hi.elim
  | closedSets => exact hi.elim
  | compactSets => exact hi.elim
  | rationalOpenBalls =>
      let e : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
      let f : {p : (Fin n → ℚ) × ℚ // 0 < p.2} → Set (Fin n → ℝ) := fun p ↦
        e '' Metric.ball (e.symm (fun j ↦ (p.1.1 j : ℝ))) (p.1.2 : ℝ)
      simpa [euclideanBorelGeneratorClass, e, f, exists_prop] using
        countable_single_parameter_family f
  | rationalOpenRectangles =>
      let f :
          {p : (Fin n → ℚ) × (Fin n → ℚ) // ∀ j, p.1 j < p.2 j} →
            Set (Fin n → ℝ) := fun p ↦
              {x | ∀ j, (p.1.1 j : ℝ) < x j ∧ x j < (p.1.2 j : ℝ)}
      simpa [euclideanBorelGeneratorClass, f, exists_prop] using
        countable_single_parameter_family f
  | rationalClosedRectangles =>
      let f :
          {p : (Fin n → ℚ) × (Fin n → ℚ) // ∀ j, p.1 j ≤ p.2 j} →
            Set (Fin n → ℝ) := fun p ↦
              {x | ∀ j, (p.1.1 j : ℝ) ≤ x j ∧ x j ≤ (p.1.2 j : ℝ)}
      simpa [euclideanBorelGeneratorClass, f, exists_prop] using
        countable_single_parameter_family f
  | rationalLeftOpenRightClosedRectangles =>
      let f :
          {p : (Fin n → ℚ) × (Fin n → ℚ) // ∀ j, p.1 j < p.2 j} →
            Set (Fin n → ℝ) := fun p ↦
              {x | ∀ j, (p.1.1 j : ℝ) < x j ∧ x j ≤ (p.1.2 j : ℝ)}
      simpa [euclideanBorelGeneratorClass, f, exists_prop] using
        countable_single_parameter_family f
  | rationalLeftClosedRightOpenRectangles =>
      let f :
          {p : (Fin n → ℚ) × (Fin n → ℚ) // ∀ j, p.1 j < p.2 j} →
            Set (Fin n → ℝ) := fun p ↦
              {x | ∀ j, (p.1.1 j : ℝ) ≤ x j ∧ x j < (p.1.2 j : ℝ)}
      simpa [euclideanBorelGeneratorClass, f, exists_prop] using
        countable_single_parameter_family f
  | rationalOpenLowerOrthants =>
      let f : (Fin n → ℚ) → Set (Fin n → ℝ) := fun b ↦ {x | ∀ j, x j < (b j : ℝ)}
      simpa [euclideanBorelGeneratorClass, f] using countable_single_parameter_family f
  | rationalClosedLowerOrthants =>
      let f : (Fin n → ℚ) → Set (Fin n → ℝ) := fun b ↦ {x | ∀ j, x j ≤ (b j : ℝ)}
      simpa [euclideanBorelGeneratorClass, f] using countable_single_parameter_family f
  | rationalOpenUpperOrthants =>
      let f : (Fin n → ℚ) → Set (Fin n → ℝ) := fun a ↦ {x | ∀ j, (a j : ℝ) < x j}
      simpa [euclideanBorelGeneratorClass, f] using countable_single_parameter_family f
  | rationalClosedUpperOrthants =>
      let f : (Fin n → ℚ) → Set (Fin n → ℝ) := fun a ↦ {x | ∀ j, (a j : ℝ) ≤ x j}
      simpa [euclideanBorelGeneratorClass, f] using countable_single_parameter_family f
