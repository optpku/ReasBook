/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap06.section03_part2

section Chap06
section Section03

open scoped Topology

/-- Helper for Theorem 6.1: the coordinate-sum linear-map candidate evaluates to the expected
finite sum `∑ j, v j • g j x₀`. -/
lemma helperForTheorem_6_1_candidateFDeriv_apply
    {n m : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    let f'fun : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
      ∑ j : Fin n,
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j)
          ((EuclideanSpace.equiv (Fin m) ℝ) (g j x₀))
    let f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      ((EuclideanSpace.equiv (Fin m) ℝ).symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp
        (f'fun.comp ((EuclideanSpace.equiv (Fin n) ℝ) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)))
    f' v =
      ∑ j : Fin n, v j • g j x₀ := by
  intro f'fun f'
  ext i
  simp [f', f'fun, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 6.1: from interiority of `x₀` in `F` and `F ⊆ E`, there is a positive
radius ball around `x₀` contained in both `F` and `E`. -/
lemma helperForTheorem_6_1_ball_subset_F_and_E
    {n : ℕ}
    {E F : Set (EuclideanSpace ℝ (Fin n))}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hFE : F ⊆ E)
    (hx₀ : x₀ ∈ interior F) :
    ∃ r > 0, Metric.ball x₀ r ⊆ F ∧ Metric.ball x₀ r ⊆ E := by
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀) with ⟨r, hrpos, hballF⟩
  refine ⟨r, hrpos, hballF, ?_⟩
  exact Set.Subset.trans hballF hFE

/-- Helper for Theorem 6.1: continuity of a fixed partial-derivative field within `F` gives
an `ε`-`δ` estimate at `x₀` for that coordinate field. -/
lemma helperForTheorem_6_1_partial_closeness_single
    {n m : ℕ}
    {F : Set (EuclideanSpace ℝ (Fin n))}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hcont : ∀ j : Fin n, ContinuousWithinAt (g j) F x₀)
    {j : Fin n}
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0,
      ∀ x, x ∈ F → dist x x₀ < δ → ‖g j x - g j x₀‖ < ε := by
  rcases (Metric.continuousWithinAt_iff.mp (hcont j)) ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x hxF hdist
  have hdistg : dist (g j x) (g j x₀) < ε := hδ hxF hdist
  simpa [dist_eq_norm] using hdistg

/-- Helper for Theorem 6.1: each within-`E` partial derivative hypothesis at a point `x ∈ F`
upgrades to a one-variable derivative statement along the coordinate line through `x` in
direction `e_j`, at parameter value `0`. -/
lemma helperForTheorem_6_1_partial_to_lineDerivWithinAt_zero
    {n m : ℕ}
    {E F : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hpartial : ∀ j : Fin n, ∀ x, x ∈ F → HasPartialDerivWithinAt E f x j (g j x))
    {j : Fin n}
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ F) :
    HasDerivWithinAt
      (fun t : ℝ => f (x + t • standardBasisVectorEuclidean n j))
      (g j x)
      {t : ℝ | x + t • standardBasisVectorEuclidean n j ∈ E}
      0 := by
  have hpart : HasPartialDerivWithinAt E f x j (g j x) := hpartial j x hx
  rw [hasDerivWithinAt_iff_tendsto_slope]
  convert hpart.2 using 1
  · ext t
    simp [slope_def_module, partialDifferenceQuotientWithin]
  · refine nhdsWithin_eq_iff_eventuallyEq.2 ?_
    filter_upwards with t
    apply propext
    constructor
    · intro ht
      have hnotSet : t ∉ ({0} : Set ℝ) := ht.2
      have hnot : ¬ t = 0 := by
        simpa [Set.mem_singleton_iff] using hnotSet
      exact ⟨hnot, ht.1⟩
    · intro ht
      have hnot : t ≠ 0 := ht.1
      have hnotSet : t ∉ ({0} : Set ℝ) := by
        simpa [Set.mem_singleton_iff] using hnot
      exact ⟨ht.2, hnotSet⟩

/-- Helper for Theorem 6.1: continuity of all coordinate partial-derivative fields at `x₀`
within `F` gives a single radius on which all coordinates are simultaneously `ε`-close,
and the same ball lies in both `F` and `E`. -/
lemma helperForTheorem_6_1_uniform_partial_closeness_on_ball
    {n m : ℕ}
    {E F : Set (EuclideanSpace ℝ (Fin n))}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hFE : F ⊆ E)
    (hx₀ : x₀ ∈ interior F)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hcont : ∀ j : Fin n, ContinuousWithinAt (g j) F x₀)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r > 0,
      Metric.ball x₀ r ⊆ F ∧
      Metric.ball x₀ r ⊆ E ∧
      ∀ j : Fin n, ∀ x, x ∈ Metric.ball x₀ r → ‖g j x - g j x₀‖ ≤ ε := by
  rcases helperForTheorem_6_1_ball_subset_F_and_E (hFE := hFE) (hx₀ := hx₀) with
    ⟨r0, hr0pos, hballF0, hballE0⟩
  by_cases hne : Nonempty (Fin n)
  · have hδexist :
      ∀ j : Fin n,
        ∃ δ > 0,
          ∀ x, x ∈ F → dist x x₀ < δ → ‖g j x - g j x₀‖ < ε := by
      intro j
      exact helperForTheorem_6_1_partial_closeness_single
        (g := g)
        (hcont := hcont)
        (j := j)
        (hε := hε)
    choose δ hδpos hδbound using hδexist
    let δmin : ℝ := Finset.univ.inf' (by simpa using hne) δ
    have hδminpos : 0 < δmin := by
      refine (Finset.lt_inf'_iff (s := Finset.univ) (H := by simpa using hne)).2 ?_
      intro j hj
      exact hδpos j
    refine ⟨min r0 δmin, lt_min hr0pos hδminpos, ?_, ?_, ?_⟩
    · intro x hx
      exact hballF0
        (Metric.mem_ball.mp (lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_left _ _)))
    · intro x hx
      exact hballE0
        (Metric.mem_ball.mp (lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_left _ _)))
    · intro j x hx
      have hxF : x ∈ F := hballF0
        (Metric.mem_ball.mp (lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_left _ _)))
      have hdistδmin : dist x x₀ < δmin :=
        lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
      have hdistδj : dist x x₀ < δ j :=
        lt_of_lt_of_le hdistδmin
          (Finset.inf'_le (s := Finset.univ) (f := δ)
            (h := Finset.mem_univ j))
      exact le_of_lt (hδbound j x hxF hdistδj)
  · have hIsEmpty : IsEmpty (Fin n) := not_nonempty_iff.mp hne
    refine ⟨r0, hr0pos, hballF0, hballE0, ?_⟩
    intro j
    exact False.elim (hIsEmpty.false j)

/-- Helper for Theorem 6.1: every vector in `ℝⁿ` is the sum of its coordinate components
along the standard basis vectors. -/
lemma helperForTheorem_6_1_sum_standardBasisVectorEuclidean_eq
    {n : ℕ}
    (h : EuclideanSpace ℝ (Fin n)) :
    (∑ j : Fin n, h j • standardBasisVectorEuclidean n j) = h := by
  simpa using
    (fderiv_apply_eq_sum_standardBasis
      (n := n)
      (m := n)
      (f' := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      h).symm

/-- Helper for Theorem 6.1: finite telescoping over successive differences on `ℕ` indices. -/
lemma helperForTheorem_6_1_sum_range_succ_sub_eq
    {α : Type*} [AddCommGroup α]
    (u : ℕ → α)
    (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => (u (i + 1) - u i)) = u n - u 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel_nf

/-- Helper for Theorem 6.1: there is a global constant controlling the sum of coordinate
norms by the ambient Euclidean norm. -/
lemma helperForTheorem_6_1_sum_norm_coordinates_le_constant_mul_norm
    {n : ℕ} :
    ∃ C > 0,
      ∀ h : EuclideanSpace ℝ (Fin n),
        (∑ j : Fin n, ‖h j‖) ≤ C * ‖h‖ := by
  let e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
    (EuclideanSpace.equiv (Fin n) ℝ)
  refine ⟨(Fintype.card (Fin n) : ℝ) * ‖e‖ + 1, by positivity, ?_⟩
  intro h
  have hsumPi :
      (∑ j : Fin n, ‖(e h) j‖) ≤ (Fintype.card (Fin n) : ℝ) * ‖e h‖ := by
    simpa [nsmul_eq_mul, Real.norm_ofNat] using
      (Pi.sum_norm_apply_le_norm (f := e h))
  have hnormLe : ‖e h‖ ≤ ‖e‖ * ‖h‖ :=
    e.le_opNorm h
  have hsumLe :
      (∑ j : Fin n, ‖h j‖) ≤ (Fintype.card (Fin n) : ℝ) * (‖e‖ * ‖h‖) := by
    calc
      (∑ j : Fin n, ‖h j‖) = (∑ j : Fin n, ‖(e h) j‖) := by rfl
      _ ≤ (Fintype.card (Fin n) : ℝ) * ‖e h‖ := hsumPi
      _ ≤ (Fintype.card (Fin n) : ℝ) * (‖e‖ * ‖h‖) := by
        gcongr
  have hnormNonneg : 0 ≤ ‖h‖ := norm_nonneg h
  have haux :
      (Fintype.card (Fin n) : ℝ) * (‖e‖ * ‖h‖)
        ≤ ((Fintype.card (Fin n) : ℝ) * ‖e‖ + 1) * ‖h‖ := by
    ring_nf
    nlinarith
  exact le_trans hsumLe haux

/-- Helper for Theorem 6.1: if `η = ε / (2 * C)` and coordinate norms satisfy
`∑ j, ‖h j‖ ≤ C * ‖h‖`, then `η * (∑ j, ‖h j‖) ≤ ε * ‖h‖`. -/
lemma helperForTheorem_6_1_eta_coordinate_sum_le_eps_norm
    {n : ℕ}
    {C ε : ℝ}
    (hCpos : 0 < C)
    (hεpos : 0 < ε)
    (hcoordBound :
      ∀ h : EuclideanSpace ℝ (Fin n),
        (∑ j : Fin n, ‖h j‖) ≤ C * ‖h‖)
    (h : EuclideanSpace ℝ (Fin n)) :
    let η : ℝ := ε / (2 * C)
    η * (∑ j : Fin n, ‖h j‖) ≤ ε * ‖h‖ := by
  intro η
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hη_nonneg : 0 ≤ η := by
    have htwoCpos : 0 < 2 * C := by positivity
    simp [η, le_of_lt (div_pos hεpos htwoCpos)]
  have hsumLe :
      η * (∑ j : Fin n, ‖h j‖) ≤ η * (C * ‖h‖) :=
    mul_le_mul_of_nonneg_left (hcoordBound h) hη_nonneg
  have hηC : η * C = ε / 2 := by
    unfold η
    field_simp [hCne]
  have hrewrite : η * (C * ‖h‖) = (ε / 2) * ‖h‖ := by
    calc
      η * (C * ‖h‖) = (η * C) * ‖h‖ := by ring
      _ = (ε / 2) * ‖h‖ := by rw [hηC]
  have hhalfLe : (ε / 2) * ‖h‖ ≤ ε * ‖h‖ := by
    have hhalfLe' : ε / 2 ≤ ε := by linarith [le_of_lt hεpos]
    exact mul_le_mul_of_nonneg_right hhalfLe' (norm_nonneg h)
  exact le_trans (le_trans hsumLe (le_of_eq hrewrite)) hhalfLe

/-- Helper for Theorem 6.1: Nat-indexed coordinate-prefix path based at `x₀` with increment
vector `h`. -/
noncomputable def helperForTheorem_6_1_coordinatePrefix_nat
    {n : ℕ}
    (x₀ h : EuclideanSpace ℝ (Fin n))
    (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  x₀ + ∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j

/-- Helper for Theorem 6.1: the Nat-indexed coordinate-prefix path starts at `x₀`. -/
lemma helperForTheorem_6_1_coordinatePrefix_nat_zero
    {n : ℕ}
    (x₀ h : EuclideanSpace ℝ (Fin n)) :
    helperForTheorem_6_1_coordinatePrefix_nat x₀ h 0 = x₀ := by
  simp [helperForTheorem_6_1_coordinatePrefix_nat]

/-- Helper for Theorem 6.1: one successor step in the Nat-indexed coordinate-prefix path adds the
next coordinate increment. -/
lemma helperForTheorem_6_1_coordinatePrefix_nat_succ
    {n : ℕ}
    (x₀ h : EuclideanSpace ℝ (Fin n))
    {k : ℕ}
    (hk : k < n) :
    helperForTheorem_6_1_coordinatePrefix_nat x₀ h (k + 1)
      = helperForTheorem_6_1_coordinatePrefix_nat x₀ h k
        + h ⟨k, hk⟩ • standardBasisVectorEuclidean n ⟨k, hk⟩ := by
  let kfin : Fin n := ⟨k, hk⟩
  have hcoeff :
      ∀ j : Fin n,
        (if (j : ℕ) < k + 1 then h j else 0)
          = (if (j : ℕ) < k then h j else 0) + (if j = kfin then h j else 0) := by
    intro j
    by_cases hjk : (j : ℕ) < k
    · have hjne : j ≠ kfin := by
        intro hEq
        have : (k : ℕ) < k := by simpa [kfin, hEq] using hjk
        exact (Nat.lt_irrefl k) this
      simp [hjk, Nat.lt_trans hjk (Nat.lt_succ_self k), hjne]
    · by_cases hjeq : j = kfin
      · subst hjeq
        simp [kfin, hk, hjk, Nat.lt_irrefl]
      · have hjneNat : (j : ℕ) ≠ k := by
          intro hEqNat
          apply hjeq
          exact Fin.ext hEqNat
        have hnotLtSucc : ¬ (j : ℕ) < k + 1 := by
          intro hlt
          have hle : (j : ℕ) ≤ k := Nat.le_of_lt_succ hlt
          rcases lt_or_eq_of_le hle with hlt' | hEqNat
          · exact hjk hlt'
          · exact hjneNat hEqNat
        simp [hjk, hjeq, hnotLtSucc]
  have hsumSplit :
      (∑ j : Fin n, (if (j : ℕ) < k + 1 then h j else 0) • standardBasisVectorEuclidean n j)
        = (∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j)
          + ∑ j : Fin n, (if j = kfin then h j else 0) • standardBasisVectorEuclidean n j := by
    calc
      (∑ j : Fin n, (if (j : ℕ) < k + 1 then h j else 0) • standardBasisVectorEuclidean n j)
          = ∑ j : Fin n,
              ((if (j : ℕ) < k then h j else 0) + (if j = kfin then h j else 0))
                • standardBasisVectorEuclidean n j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [hcoeff j]
      _ = ∑ j : Fin n,
            ((if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j
              + (if j = kfin then h j else 0) • standardBasisVectorEuclidean n j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [add_smul]
      _ = (∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j)
            + ∑ j : Fin n, (if j = kfin then h j else 0) • standardBasisVectorEuclidean n j := by
              simp [Finset.sum_add_distrib]
  have hsingle :
      (∑ j : Fin n, (if j = kfin then h j else 0) • standardBasisVectorEuclidean n j)
        = h kfin • standardBasisVectorEuclidean n kfin := by
    classical
    simpa using
      (Fintype.sum_eq_single kfin
        (fun j hj => by simp [hj])
        (by simp))
  calc
    helperForTheorem_6_1_coordinatePrefix_nat x₀ h (k + 1)
        = x₀ +
            ∑ j : Fin n,
              (if (j : ℕ) < k + 1 then h j else 0) • standardBasisVectorEuclidean n j := rfl
    _ = x₀ +
          ((∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j)
            + ∑ j : Fin n, (if j = kfin then h j else 0) • standardBasisVectorEuclidean n j) := by
          rw [hsumSplit]
    _ = (x₀ +
          ∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j)
          + ∑ j : Fin n, (if j = kfin then h j else 0) • standardBasisVectorEuclidean n j := by
          abel_nf
    _ = helperForTheorem_6_1_coordinatePrefix_nat x₀ h k
          + ∑ j : Fin n, (if j = kfin then h j else 0) • standardBasisVectorEuclidean n j := rfl
    _ = helperForTheorem_6_1_coordinatePrefix_nat x₀ h k
          + h kfin • standardBasisVectorEuclidean n kfin := by
          rw [hsingle]

/-- Helper for Theorem 6.1: the final Nat-indexed coordinate-prefix node is `x₀ + h`. -/
lemma helperForTheorem_6_1_coordinatePrefix_nat_at_top
    {n : ℕ}
    (x₀ h : EuclideanSpace ℝ (Fin n)) :
    helperForTheorem_6_1_coordinatePrefix_nat x₀ h n = x₀ + h := by
  calc
    helperForTheorem_6_1_coordinatePrefix_nat x₀ h n
        = x₀ + ∑ j : Fin n, h j • standardBasisVectorEuclidean n j := by
            simp [helperForTheorem_6_1_coordinatePrefix_nat, Fin.is_lt]
    _ = x₀ + h := by
          rw [helperForTheorem_6_1_sum_standardBasisVectorEuclidean_eq (n := n) h]

/-- Helper for Theorem 6.1: one coordinate-segment increment has remainder controlled by
the uniform bound on the corresponding partial field along that segment. -/
lemma helperForTheorem_6_1_coordinate_segment_error_package
    {n m : ℕ}
    {E F : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ p : EuclideanSpace ℝ (Fin n)}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    {j : Fin n}
    {hj η r : ℝ}
    (hpartialLine :
      ∀ x, x ∈ F →
        HasDerivWithinAt
          (fun t : ℝ => f (x + t • standardBasisVectorEuclidean n j))
          (g j x)
          {t : ℝ | x + t • standardBasisVectorEuclidean n j ∈ E}
          0)
    (hballF : Metric.ball x₀ r ⊆ F)
    (hclose : ∀ x, x ∈ Metric.ball x₀ r → ‖g j x - g j x₀‖ ≤ η)
    (hsegE : ∀ t : ℝ, t ∈ segment ℝ (0 : ℝ) hj →
      p + t • standardBasisVectorEuclidean n j ∈ E)
    (hsegBall : ∀ t : ℝ, t ∈ segment ℝ (0 : ℝ) hj →
      p + t • standardBasisVectorEuclidean n j ∈ Metric.ball x₀ r) :
    ‖(f (p + hj • standardBasisVectorEuclidean n j) - f p) - hj • g j x₀‖ ≤ η * ‖hj‖ := by
  let φ : ℝ → EuclideanSpace ℝ (Fin m) :=
    fun t => f (p + t • standardBasisVectorEuclidean n j) - t • g j x₀
  have hderivφ :
      ∀ t : ℝ, t ∈ segment ℝ (0 : ℝ) hj →
        HasDerivWithinAt φ (g j (p + t • standardBasisVectorEuclidean n j) - g j x₀)
          (segment ℝ (0 : ℝ) hj) t := by
    intro t ht
    have hxBall : p + t • standardBasisVectorEuclidean n j ∈ Metric.ball x₀ r := hsegBall t ht
    have hxF : p + t • standardBasisVectorEuclidean n j ∈ F := hballF hxBall
    have houter :
        HasDerivWithinAt
          (fun u : ℝ => f ((p + t • standardBasisVectorEuclidean n j) + u • standardBasisVectorEuclidean n j))
          (g j (p + t • standardBasisVectorEuclidean n j))
          {u : ℝ | (p + t • standardBasisVectorEuclidean n j) + u • standardBasisVectorEuclidean n j ∈ E}
          0 := hpartialLine _ hxF
    have hinner : HasDerivWithinAt (fun z : ℝ => z - t) 1 (segment ℝ (0 : ℝ) hj) t := by
      simpa [sub_eq_add_neg] using
        (hasDerivWithinAt_id (x := t) (s := segment ℝ (0 : ℝ) hj)).sub_const t
    have hmaps : Set.MapsTo (fun z : ℝ => z - t) (segment ℝ (0 : ℝ) hj)
        {u : ℝ |
          (p + t • standardBasisVectorEuclidean n j) + u • standardBasisVectorEuclidean n j ∈ E} := by
      intro z hz
      have hzE : p + z • standardBasisVectorEuclidean n j ∈ E := hsegE z hz
      have hrewrite :
          (p + t • standardBasisVectorEuclidean n j) + (z - t) • standardBasisVectorEuclidean n j
            = p + z • standardBasisVectorEuclidean n j := by
        calc
          (p + t • standardBasisVectorEuclidean n j) + (z - t) • standardBasisVectorEuclidean n j
              = p + (t • standardBasisVectorEuclidean n j
                  + (z - t) • standardBasisVectorEuclidean n j) := by
                  abel_nf
          _ = p + ((t + (z - t)) • standardBasisVectorEuclidean n j) := by rw [add_smul]
          _ = p + z • standardBasisVectorEuclidean n j := by ring_nf
      simpa [hrewrite] using hzE
    have hcomp :=
      HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
        (x := t)
        (hl := houter.hasFDerivWithinAt)
        (hf := hinner)
        (hst := hmaps)
        (hy := by ring_nf)
    have hbase :
        HasDerivWithinAt
          (fun z : ℝ => f (p + z • standardBasisVectorEuclidean n j))
          (g j (p + t • standardBasisVectorEuclidean n j))
          (segment ℝ (0 : ℝ) hj)
          t := by
      have hcomp' :
          HasDerivWithinAt
            (((fun u : ℝ =>
                f ((p + t • standardBasisVectorEuclidean n j) +
                    u • standardBasisVectorEuclidean n j)) ∘
                fun z : ℝ => z - t))
            (g j (p + t • standardBasisVectorEuclidean n j))
            (segment ℝ (0 : ℝ) hj)
            t := by
        simpa using hcomp
      convert hcomp' using 1
      funext z
      ext i
      simp [sub_eq_add_neg, add_assoc, add_smul]
    have hsmul :
        HasDerivWithinAt (fun z : ℝ => z • g j x₀) (g j x₀)
          (segment ℝ (0 : ℝ) hj) t := by
      simpa using
        (hasDerivWithinAt_id (x := t) (s := segment ℝ (0 : ℝ) hj)).smul_const (g j x₀)
    have hφ :
        HasDerivWithinAt
          (fun z : ℝ => f (p + z • standardBasisVectorEuclidean n j) - z • g j x₀)
          (g j (p + t • standardBasisVectorEuclidean n j) - g j x₀)
          (segment ℝ (0 : ℝ) hj)
          t := hbase.sub hsmul
    simpa [φ] using hφ
  have hboundDer :
      ∀ t : ℝ, t ∈ segment ℝ (0 : ℝ) hj →
        ‖g j (p + t • standardBasisVectorEuclidean n j) - g j x₀‖ ≤ η := by
    intro t ht
    exact hclose _ (hsegBall t ht)
  have hsegment :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := φ)
      (f' := fun t : ℝ => g j (p + t • standardBasisVectorEuclidean n j) - g j x₀)
      (s := segment ℝ (0 : ℝ) hj)
      (x := (0 : ℝ))
      (y := hj)
      (C := η)
      hderivφ
      hboundDer
      (convex_segment (0 : ℝ) hj)
      (left_mem_segment ℝ (0 : ℝ) hj)
      (right_mem_segment ℝ (0 : ℝ) hj)
  simpa [φ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsegment

/-- Helper for Theorem 6.1: a local linear remainder bound implies `HasFDerivWithinAt`. -/
lemma helperForTheorem_6_1_hasFDerivWithinAt_of_linear_remainder_bound
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hbound :
      ∀ ε > 0, ∃ δ > 0,
        ∀ x, x ∈ E → dist x x₀ < δ →
          ‖f x - f x₀ - f' (x - x₀)‖ ≤ ε * ‖x - x₀‖) :
    HasFDerivWithinAt f f' E x₀ := by
  rw [hasFDerivWithinAt_iff_tendsto]
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  rcases hbound (ε / 2) (half_pos hε) with ⟨δ, hδpos, hδ⟩
  filter_upwards [inter_mem_nhdsWithin E (Metric.ball_mem_nhds x₀ hδpos)] with x hx
  have hxE : x ∈ E := hx.1
  have hdist : dist x x₀ < δ := Metric.mem_ball.mp hx.2
  have hnumBound : ‖f x - f x₀ - f' (x - x₀)‖ ≤ (ε / 2) * ‖x - x₀‖ :=
    hδ x hxE hdist
  have hnormNonneg : 0 ≤ ‖x - x₀‖ := norm_nonneg (x - x₀)
  have hratioLeHalf :
      ‖x - x₀‖⁻¹ * ‖f x - f x₀ - f' (x - x₀)‖ ≤ ε / 2 := by
    by_cases hnormZero : ‖x - x₀‖ = 0
    · have hnumEqZero : ‖f x - f x₀ - f' (x - x₀)‖ = 0 := by
        have hnumLeZero : ‖f x - f x₀ - f' (x - x₀)‖ ≤ 0 := by
          simpa [hnormZero] using hnumBound
        exact le_antisymm hnumLeZero (norm_nonneg _)
      have hratioEqZero :
          ‖x - x₀‖⁻¹ * ‖f x - f x₀ - f' (x - x₀)‖ = 0 := by
        simp [hnormZero]
      rw [hratioEqZero]
      exact le_of_lt (half_pos hε)
    · have hmul :=
        mul_le_mul_of_nonneg_left hnumBound (inv_nonneg.mpr hnormNonneg)
      have hcancel : ‖x - x₀‖⁻¹ * ((ε / 2) * ‖x - x₀‖) = ε / 2 := by
        calc
          ‖x - x₀‖⁻¹ * ((ε / 2) * ‖x - x₀‖)
              = (ε / 2) * (‖x - x₀‖⁻¹ * ‖x - x₀‖) := by ring
          _ = ε / 2 := by rw [inv_mul_cancel₀ hnormZero, mul_one]
      exact hmul.trans_eq hcancel
  have hratioLt : ‖x - x₀‖⁻¹ * ‖f x - f x₀ - f' (x - x₀)‖ < ε :=
    lt_of_le_of_lt hratioLeHalf (half_lt_self hε)
  have hratioNonneg :
      0 ≤ ‖x - x₀‖⁻¹ * ‖f x - f x₀ - f' (x - x₀)‖ :=
    mul_nonneg (inv_nonneg.mpr hnormNonneg) (norm_nonneg _)
  simpa [Real.dist_eq, abs_of_nonneg hratioNonneg] using hratioLt

/-- Theorem 6.1: Let `E ⊆ ℝⁿ`, let `f : ℝⁿ → ℝᵐ` be an ambient extension of a map on `E`,
let `F ⊆ E`, and let `x₀` be an interior point of `F` (equivalently, there is `r > 0` with
`Metric.ball x₀ r ⊆ F`). Assume that for each `j ∈ {1, …, n}` there is a
partial-derivative field `g j` on `F` such that
`HasPartialDerivWithinAt E f x j (g j x)` for every `x ∈ F`, and `g j` is continuous at `x₀`
when restricted to `F`. Then `f` is differentiable at `x₀` within `E`, and its derivative is
the linear map `v ↦ ∑ j, v j • g j x₀`. -/
theorem hasFDerivAt_of_continuous_partialDerivWithinAt
    {n m : ℕ}
    {E F : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hFE : F ⊆ E)
    (hx₀ : x₀ ∈ interior F)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hpartial : ∀ j : Fin n, ∀ x, x ∈ F → HasPartialDerivWithinAt E f x j (g j x))
    (hcont : ∀ j : Fin n, ContinuousWithinAt (g j) F x₀) :
    ∃ f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasFDerivWithinAt f f' E x₀ ∧
        ∀ v : EuclideanSpace ℝ (Fin n),
          f' v = ∑ j : Fin n, v j • g j x₀ := by
  let f'fun : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ∑ j : Fin n,
      ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j)
        ((EuclideanSpace.equiv (Fin m) ℝ) (g j x₀))
  let f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ((EuclideanSpace.equiv (Fin m) ℝ).symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp
      (f'fun.comp ((EuclideanSpace.equiv (Fin n) ℝ) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)))
  refine ⟨f', ?_, ?_⟩
  · have hpartialLine :
      ∀ j : Fin n, ∀ x, x ∈ F →
        HasDerivWithinAt
          (fun t : ℝ => f (x + t • standardBasisVectorEuclidean n j))
          (g j x)
          {t : ℝ | x + t • standardBasisVectorEuclidean n j ∈ E}
          0 := by
      intro j x hx
      exact helperForTheorem_6_1_partial_to_lineDerivWithinAt_zero
        (g := g)
        (hpartial := hpartial)
        hx
    have huniformCloseness :
      ∀ ε > 0,
        ∃ r > 0,
          Metric.ball x₀ r ⊆ F ∧
          Metric.ball x₀ r ⊆ E ∧
          ∀ j : Fin n, ∀ x, x ∈ Metric.ball x₀ r → ‖g j x - g j x₀‖ ≤ ε := by
      intro ε hε
      exact helperForTheorem_6_1_uniform_partial_closeness_on_ball
        (hFE := hFE)
        (hx₀ := hx₀)
        (g := g)
        (hcont := hcont)
        (hε := hε)
    refine helperForTheorem_6_1_hasFDerivWithinAt_of_linear_remainder_bound (f' := f') ?_
    intro ε hε
    have hsumStandardBasis :
        ∀ h : EuclideanSpace ℝ (Fin n),
          (∑ j : Fin n, h j • standardBasisVectorEuclidean n j) = h := by
      intro h
      exact helperForTheorem_6_1_sum_standardBasisVectorEuclidean_eq (n := n) h
    have htelescopingNat :
        ∀ u : ℕ → EuclideanSpace ℝ (Fin m),
          ∀ N : ℕ,
            Finset.sum (Finset.range N) (fun i => (u (i + 1) - u i)) = u N - u 0 := by
      intro u N
      exact helperForTheorem_6_1_sum_range_succ_sub_eq (u := u) N
    rcases helperForTheorem_6_1_sum_norm_coordinates_le_constant_mul_norm (n := n) with
      ⟨C, hCpos, hCbound⟩
    have hcoordBound :
        ∀ h : EuclideanSpace ℝ (Fin n),
          (∑ j : Fin n, ‖h j‖) ≤ C * ‖h‖ :=
      hCbound
    let η : ℝ := ε / (2 * C)
    have hηpos : 0 < η := by
      have htwoCpos : 0 < 2 * C := by positivity
      exact div_pos hε htwoCpos
    rcases huniformCloseness η hηpos with ⟨r, hrpos, hballF, hballE, hclose⟩
    have hη_nonneg : 0 ≤ η := le_of_lt hηpos
    refine ⟨r / C, div_pos hrpos hCpos, ?_⟩
    intro x hxE hxdist
    let h : EuclideanSpace ℝ (Fin n) := x - x₀
    have hnormh : ‖h‖ < r / C := by
      simpa [h, dist_eq_norm] using hxdist
    have hcoordSum : (∑ j : Fin n, ‖h j‖) ≤ C * ‖h‖ := hcoordBound h
    have hCne : C ≠ 0 := ne_of_gt hCpos
    have hcoordLt : (∑ j : Fin n, ‖h j‖) < r := by
      have hmul : C * ‖h‖ < C * (r / C) :=
        mul_lt_mul_of_pos_left hnormh hCpos
      have hrewrite : C * (r / C) = r := by
        field_simp [hCne]
      exact lt_of_le_of_lt hcoordSum (by simpa [hrewrite] using hmul)
    have hnormLeCoord : ‖h‖ ≤ ∑ j : Fin n, ‖h j‖ := by
      calc
        ‖h‖ = ‖∑ j : Fin n, h j • standardBasisVectorEuclidean n j‖ := by
              rw [helperForTheorem_6_1_sum_standardBasisVectorEuclidean_eq (n := n) h]
        _ ≤ ∑ j : Fin n, ‖h j • standardBasisVectorEuclidean n j‖ :=
              norm_sum_le _ _
        _ = ∑ j : Fin n, ‖h j‖ := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              calc
                ‖h j • standardBasisVectorEuclidean n j‖
                    = ‖h j‖ * ‖standardBasisVectorEuclidean n j‖ := norm_smul _ _
                _ = ‖h j‖ * ‖(1 : ℝ)‖ := by
                      simp [standardBasisVectorEuclidean, EuclideanSpace.norm_single]
                _ = ‖h j‖ := by simp
    have hxBall : x ∈ Metric.ball x₀ r := by
      refine Metric.mem_ball.mpr ?_
      have hdistEq : dist x x₀ = ‖h‖ := by
        simpa [h, dist_eq_norm]
      have hbound : ‖h‖ < r := lt_of_le_of_lt hnormLeCoord hcoordLt
      simpa [hdistEq] using hbound
    have hxF : x ∈ F := hballF hxBall
    have hxE' : x ∈ E := hballE hxBall
    have hxrepr : x₀ + h = x := by
      simp [h, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hf'apply : f' h = ∑ j : Fin n, h j • g j x₀ := by
      simpa [f'fun, f'] using helperForTheorem_6_1_candidateFDeriv_apply (g := g) x₀ h
    have hprefix0 : helperForTheorem_6_1_coordinatePrefix_nat x₀ h 0 = x₀ :=
      helperForTheorem_6_1_coordinatePrefix_nat_zero x₀ h
    have hprefixN : helperForTheorem_6_1_coordinatePrefix_nat x₀ h n = x₀ + h :=
      helperForTheorem_6_1_coordinatePrefix_nat_at_top x₀ h
    have hboundToProve :
        ‖f (x₀ + h) - f x₀ - ∑ j : Fin n, h j • g j x₀‖ ≤ ε * ‖h‖ := by
      let p : ℕ → EuclideanSpace ℝ (Fin n) :=
        helperForTheorem_6_1_coordinatePrefix_nat x₀ h
      have hprefixBall :
          ∀ k ≤ n, p k ∈ Metric.ball x₀ r := by
        intro k hk
        refine Metric.mem_ball.mpr ?_
        have hnormSum :
            ‖∑ j : Fin n,
                (if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j‖
              ≤ ∑ j : Fin n, ‖(if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j‖ :=
          norm_sum_le _ _
        have hsumLe :
            (∑ j : Fin n, ‖(if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j‖)
              ≤ ∑ j : Fin n, ‖h j‖ := by
          refine Finset.sum_le_sum ?_
          intro j hj
          by_cases hjk : (j : ℕ) < k
          · calc
              ‖(if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j‖
                  = ‖h j • standardBasisVectorEuclidean n j‖ := by simp [hjk]
              _ = ‖h j‖ * ‖standardBasisVectorEuclidean n j‖ := norm_smul _ _
              _ = ‖h j‖ := by
                    simp [standardBasisVectorEuclidean, EuclideanSpace.norm_single]
              _ ≤ ‖h j‖ := le_rfl
          · simp [hjk]
        have hdist :
            dist (p k) x₀
              = ‖∑ j : Fin n,
                  (if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j‖ := by
          simp [p, helperForTheorem_6_1_coordinatePrefix_nat, dist_eq_norm, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]
        have hlt :
            ‖∑ j : Fin n,
                (if (j : ℕ) < k then h j else 0) • standardBasisVectorEuclidean n j‖ < r :=
          lt_of_le_of_lt (le_trans hnormSum hsumLe) hcoordLt
        simpa [hdist] using hlt
      have hsegmentBall :
          ∀ {k : ℕ} (hk : k < n), ∀ t : ℝ,
            t ∈ segment ℝ (0 : ℝ) (h ⟨k, hk⟩) →
            p k + t • standardBasisVectorEuclidean n ⟨k, hk⟩ ∈ Metric.ball x₀ r := by
        intro k hk t ht
        let kfin : Fin n := ⟨k, hk⟩
        have hpkBall : p k ∈ Metric.ball x₀ r :=
          hprefixBall k (Nat.le_of_lt hk)
        have hpksuccBall : p (k + 1) ∈ Metric.ball x₀ r :=
          hprefixBall (k + 1) (Nat.succ_le_of_lt hk)
        have hstep : p (k + 1) = p k + h kfin • standardBasisVectorEuclidean n kfin := by
          simpa [p, kfin] using helperForTheorem_6_1_coordinatePrefix_nat_succ x₀ h hk
        have htVec :
            t • standardBasisVectorEuclidean n kfin ∈
              segment ℝ (0 : EuclideanSpace ℝ (Fin n))
                (h kfin • standardBasisVectorEuclidean n kfin) := by
          rw [segment_eq_image_lineMap] at ht
          rcases ht with ⟨u, hu, rfl⟩
          rw [segment_eq_image_lineMap]
          refine ⟨u, hu, ?_⟩
          simpa [kfin, AffineMap.lineMap_apply, smul_smul]
        have hmemSegTranslate :
            p k + t • standardBasisVectorEuclidean n kfin ∈
              segment ℝ (p k + (0 : EuclideanSpace ℝ (Fin n)))
                (p k + h kfin • standardBasisVectorEuclidean n kfin) :=
          (mem_segment_translate ℝ (p k)).2 htVec
        have hmemSeg :
            p k + t • standardBasisVectorEuclidean n kfin ∈
              segment ℝ (p k) (p (k + 1)) := by
          simpa [hstep] using hmemSegTranslate
        exact (Convex.segment_subset (convex_ball x₀ r) hpkBall hpksuccBall) hmemSeg
      have hstepBound :
          ∀ {k : ℕ} (hk : k < n),
            ‖(f (p (k + 1)) - f (p k)) - h ⟨k, hk⟩ • g ⟨k, hk⟩ x₀‖
              ≤ η * ‖h ⟨k, hk⟩‖ := by
        intro k hk
        let kfin : Fin n := ⟨k, hk⟩
        have hpkF : p k ∈ F := hballF (hprefixBall k (Nat.le_of_lt hk))
        have hsegE :
            ∀ t : ℝ, t ∈ segment ℝ (0 : ℝ) (h kfin) →
              p k + t • standardBasisVectorEuclidean n kfin ∈ E := by
          intro t ht
          exact hballE (hsegmentBall hk t ht)
        have hsegBall :
            ∀ t : ℝ, t ∈ segment ℝ (0 : ℝ) (h kfin) →
              p k + t • standardBasisVectorEuclidean n kfin ∈ Metric.ball x₀ r := by
          intro t ht
          exact hsegmentBall hk t ht
        have hstepRaw :=
          helperForTheorem_6_1_coordinate_segment_error_package
            (g := g)
            (x₀ := x₀)
            (p := p k)
            (j := kfin)
            (hj := h kfin)
            (η := η)
            (r := r)
            (hpartialLine := fun x hx => hpartialLine kfin x hx)
            (hballF := hballF)
            (hclose := fun x hx => hclose kfin x hx)
            (hsegE := hsegE)
            (hsegBall := hsegBall)
        have hstepEq : p (k + 1) = p k + h kfin • standardBasisVectorEuclidean n kfin := by
          simpa [p, kfin] using helperForTheorem_6_1_coordinatePrefix_nat_succ x₀ h hk
        simpa [hstepEq, kfin] using hstepRaw
      have hsumSucc :
          ∀ {k : ℕ} (hk : k < n),
            (∑ j : Fin n, (if (j : ℕ) < k + 1 then h j else 0) • g j x₀)
              = (∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • g j x₀)
                + h ⟨k, hk⟩ • g ⟨k, hk⟩ x₀ := by
        intro k hk
        let kfin : Fin n := ⟨k, hk⟩
        have hcoeff :
            ∀ j : Fin n,
              (if (j : ℕ) < k + 1 then h j else 0)
                = (if (j : ℕ) < k then h j else 0) + (if j = kfin then h j else 0) := by
          intro j
          by_cases hjk : (j : ℕ) < k
          · have hjne : j ≠ kfin := by
              intro hEq
              have : (k : ℕ) < k := by simpa [kfin, hEq] using hjk
              exact (Nat.lt_irrefl k) this
            simp [hjk, Nat.lt_trans hjk (Nat.lt_succ_self k), hjne]
          · by_cases hjeq : j = kfin
            · subst hjeq
              simp [kfin, hk, hjk, Nat.lt_irrefl]
            · have hjneNat : (j : ℕ) ≠ k := by
                intro hEqNat
                apply hjeq
                exact Fin.ext hEqNat
              have hnotLtSucc : ¬ (j : ℕ) < k + 1 := by
                intro hlt
                have hle : (j : ℕ) ≤ k := Nat.le_of_lt_succ hlt
                rcases lt_or_eq_of_le hle with hlt' | hEqNat
                · exact hjk hlt'
                · exact hjneNat hEqNat
              simp [hjk, hjeq, hnotLtSucc]
        have hsumSplit :
            (∑ j : Fin n, (if (j : ℕ) < k + 1 then h j else 0) • g j x₀)
              = (∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • g j x₀)
                + ∑ j : Fin n, (if j = kfin then h j else 0) • g j x₀ := by
          calc
            (∑ j : Fin n, (if (j : ℕ) < k + 1 then h j else 0) • g j x₀)
                = ∑ j : Fin n,
                    ((if (j : ℕ) < k then h j else 0) + (if j = kfin then h j else 0)) • g j x₀ := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [hcoeff j]
            _ = ∑ j : Fin n,
                  ((if (j : ℕ) < k then h j else 0) • g j x₀
                    + (if j = kfin then h j else 0) • g j x₀) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [add_smul]
            _ = (∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • g j x₀)
                  + ∑ j : Fin n, (if j = kfin then h j else 0) • g j x₀ := by
                    simp [Finset.sum_add_distrib]
        have hsingle :
            (∑ j : Fin n, (if j = kfin then h j else 0) • g j x₀)
              = h kfin • g kfin x₀ := by
          classical
          simpa using
            (Fintype.sum_eq_single kfin
              (fun j hj => by simp [hj])
              (by simp))
        calc
          (∑ j : Fin n, (if (j : ℕ) < k + 1 then h j else 0) • g j x₀)
              = (∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • g j x₀)
                + ∑ j : Fin n, (if j = kfin then h j else 0) • g j x₀ := hsumSplit
          _ = (∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • g j x₀)
                + h kfin • g kfin x₀ := by rw [hsingle]
      let u : ℕ → EuclideanSpace ℝ (Fin m) :=
        fun k => f (p k) - ∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • g j x₀
      have huStep :
          ∀ {k : ℕ} (hk : k < n),
            u (k + 1) - u k
              = (f (p (k + 1)) - f (p k)) - h ⟨k, hk⟩ • g ⟨k, hk⟩ x₀ := by
        intro k hk
        change (f (p (k + 1)) - ∑ j : Fin n, (if (j : ℕ) < k + 1 then h j else 0) • g j x₀)
              - (f (p k) - ∑ j : Fin n, (if (j : ℕ) < k then h j else 0) • g j x₀)
            = (f (p (k + 1)) - f (p k)) - h ⟨k, hk⟩ • g ⟨k, hk⟩ x₀
        rw [hsumSucc hk]
        abel_nf
      have hsumNormLe :
          (∑ i ∈ Finset.range n, ‖u (i + 1) - u i‖)
            ≤ ∑ i ∈ Finset.range n, (if hi : i < n then η * ‖h ⟨i, hi⟩‖ else 0) := by
        refine Finset.sum_le_sum ?_
        intro i hiRange
        have hi : i < n := Finset.mem_range.mp hiRange
        have hstepNorm : ‖u (i + 1) - u i‖ ≤ η * ‖h ⟨i, hi⟩‖ := by
          simpa [huStep hi] using hstepBound (k := i) hi
        simpa [hi] using hstepNorm
      have hrangeEtaEq :
          (∑ i ∈ Finset.range n, (if hi : i < n then η * ‖h ⟨i, hi⟩‖ else 0))
            = η * ∑ j : Fin n, ‖h j‖ := by
        have hsum :=
          (Fin.sum_univ_eq_sum_range
            (f := fun i : ℕ => if hi : i < n then η * ‖h ⟨i, hi⟩‖ else 0)
            (n := n))
        have hleft :
            (∑ i : Fin n, (if hi : (i : ℕ) < n then η * ‖h ⟨(i : ℕ), hi⟩‖ else 0))
              = η * ∑ j : Fin n, ‖h j‖ := by
          calc
            (∑ i : Fin n, (if hi : (i : ℕ) < n then η * ‖h ⟨(i : ℕ), hi⟩‖ else 0))
                = ∑ i : Fin n, η * ‖h i‖ := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    simp [Fin.is_lt i]
            _ = η * ∑ j : Fin n, ‖h j‖ := by
                  rw [Finset.mul_sum]
        exact Eq.trans hsum.symm hleft
      have hsumNormLe' :
          (∑ i ∈ Finset.range n, ‖u (i + 1) - u i‖) ≤ η * ∑ j : Fin n, ‖h j‖ := by
        exact le_trans hsumNormLe (le_of_eq hrangeEtaEq)
      have huDiffBound :
          ‖u n - u 0‖ ≤ η * ∑ j : Fin n, ‖h j‖ := by
        have htel :
            (∑ i ∈ Finset.range n, (u (i + 1) - u i)) = u n - u 0 :=
          htelescopingNat u n
        calc
          ‖u n - u 0‖ = ‖∑ i ∈ Finset.range n, (u (i + 1) - u i)‖ := by
                          rw [← htel]
          _ ≤ ∑ i ∈ Finset.range n, ‖u (i + 1) - u i‖ := norm_sum_le _ _
          _ ≤ η * ∑ j : Fin n, ‖h j‖ := hsumNormLe'
      have hu0 : u 0 = f x₀ := by
        simp [u, p, hprefix0]
      have huN : u n = f (x₀ + h) - ∑ j : Fin n, h j • g j x₀ := by
        simp [u, p, hprefixN, Fin.is_lt]
      have hpathBound :
          ‖f (x₀ + h) - f x₀ - ∑ j : Fin n, h j • g j x₀‖
            ≤ η * ∑ j : Fin n, ‖h j‖ := by
        have htargetEq :
            f (x₀ + h) - f x₀ - ∑ j : Fin n, h j • g j x₀ = u n - u 0 := by
          rw [huN, hu0]
          abel_nf
        calc
          ‖f (x₀ + h) - f x₀ - ∑ j : Fin n, h j • g j x₀‖ = ‖u n - u 0‖ := by
                rw [htargetEq]
          _ ≤ η * ∑ j : Fin n, ‖h j‖ := huDiffBound
      have hηToEps :
          η * (∑ j : Fin n, ‖h j‖) ≤ ε * ‖h‖ := by
        simpa [η] using
          (helperForTheorem_6_1_eta_coordinate_sum_le_eps_norm
            (n := n)
            (C := C)
            (ε := ε)
            hCpos
            hε
            hcoordBound
            h)
      exact le_trans hpathBound hηToEps
    have htarget : ‖f x - f x₀ - f' (x - x₀)‖ ≤ ε * ‖x - x₀‖ := by
      have hsub : x - x₀ = h := by simp [h]
      calc
        ‖f x - f x₀ - f' (x - x₀)‖
            = ‖f (x₀ + h) - f x₀ - f' h‖ := by
                simp [hxrepr, hsub]
        _ = ‖f (x₀ + h) - f x₀ - ∑ j : Fin n, h j • g j x₀‖ := by
              rw [hf'apply]
        _ ≤ ε * ‖h‖ := hboundToProve
        _ = ε * ‖x - x₀‖ := by simp [h]
    exact htarget
  · intro v
    simpa [f'fun, f'] using helperForTheorem_6_1_candidateFDeriv_apply (g := g) x₀ v


end Section03
end Chap06
