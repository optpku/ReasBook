/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part9

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Theorem 25.6: once the boundary directional derivative in the admissible direction
is not `⊥`, the fixed interior comparison points at `x + t • u ± (ρ/2)eⱼ` give a common
coordinate box for every support realizer chosen along the ray. -/
lemma helperForTheorem_25_6_uniform_coordinate_bound_on_admissibleRay_from_center_secants
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x u : Fin n → Real} {t ρ : Real}
    (_hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (_ht : 0 < t)
    (hxtuInt : x + t • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hdirNeBot : upperDirectionalDerivativeAt f x u ≠ ⊥)
    (hρpos : 0 < ρ)
    (hplusInt :
      ∀ j : Fin n,
        let e : Fin n → Real := Pi.single j (1 : Real)
        x + t • u + (ρ / 2) • e ∈
          interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hminusInt :
      ∀ j : Fin n,
        let e : Fin n → Real := Pi.single j (1 : Real)
        x + t • u - (ρ / 2) • e ∈
          interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    {qSeq : ℕ → Fin n → Real}
    (hqSeqSub :
      ∀ i : ℕ,
        let xi := x + (t / ((i : Real) + 1)) • u
        qSeq i ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f xi))
    (hqSeqPair :
      ∀ i : ℕ,
        upperDirectionalDerivativeAt f (x + (t / ((i : Real) + 1)) • u) u =
          (((dotProduct (qSeq i) u : Real) : EReal))) :
    ∃ M : Fin n → Real, ∀ i : ℕ, ∀ j : Fin n, |qSeq i j| ≤ M j := by
  let _ := hf_closed
  let _ := hxtuInt
  let _ := hqSeqPair
  let z : Fin n → Real := x + t • u
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hdirLePair :
      ∀ i : ℕ,
        upperDirectionalDerivativeAt f x u ≤ (((dotProduct (qSeq i) u : Real) : EReal)) := by
    intro i
    let s : Real := t / ((i : Real) + 1)
    have hsPos : 0 < s := by
      dsimp [s]
      positivity
    -- Every selected interior realizer lies at a positive step on the admissible ray.
    simpa [s] using
      helperForTheorem_25_6_upperDirectionalDerivative_le_pairing_of_preimageSubgradient_on_positive_rayStep
        (f := f) hf _hx hsPos (hqSeqSub i)
  have hdirNeTop : upperDirectionalDerivativeAt f x u ≠ ⊤ := by
    have hfiniteLe := hdirLePair 0
    intro htop
    have : (⊤ : EReal) ≤ (((dotProduct (qSeq 0) u : Real) : EReal)) := by
      simpa [htop] using hfiniteLe
    have htopCoe : (((dotProduct (qSeq 0) u : Real) : EReal)) = ⊤ := top_le_iff.mp this
    simpa using htopCoe
  lift upperDirectionalDerivativeAt f x u to Real using ⟨hdirNeTop, hdirNeBot⟩ with d hd
  have hpairLower :
      ∀ i : ℕ, d ≤ dotProduct (qSeq i) u := by
    intro i
    have hpairLowerE :
        (((d : Real) : EReal)) ≤ (((dotProduct (qSeq i) u : Real) : EReal)) := by
      simpa [hd] using hdirLePair i
    exact_mod_cast hpairLowerE
  have hplusData :
      ∀ j : Fin n, ∃ v : Fin n → Real,
        let e : Fin n → Real := Pi.single j (1 : Real)
        v ∈
          ((dotProductEquiv Real (Fin n)) ⁻¹'
            subdifferentialAt f (z + (ρ / 2) • e)) := by
    intro j
    have hzjInt :
        let e : Fin n → Real := Pi.single j (1 : Real)
        z + (ρ / 2) • e ∈
          interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      simpa [z] using hplusInt j
    rcases
        (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
          (f := f) hf hzjInt).1 with
      ⟨v, hv⟩
    exact ⟨v, hv⟩
  have hminusData :
      ∀ j : Fin n, ∃ v : Fin n → Real,
        let e : Fin n → Real := Pi.single j (1 : Real)
        v ∈
          ((dotProductEquiv Real (Fin n)) ⁻¹'
            subdifferentialAt f (z - (ρ / 2) • e)) := by
    intro j
    have hzjInt :
        let e : Fin n → Real := Pi.single j (1 : Real)
        z - (ρ / 2) • e ∈
          interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      simpa [z] using hminusInt j
    rcases
        (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
          (f := f) hf hzjInt).1 with
      ⟨v, hv⟩
    exact ⟨v, hv⟩
  choose vPlus hvPlus using hplusData
  choose vMinus hvMinus using hminusData
  let M : Fin n → Real := fun j =>
    max
      (|vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|)|)
      (|vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|)|)
  refine ⟨M, ?_⟩
  intro i j
  let s : Real := t / ((i : Real) + 1)
  have hsPos : 0 < s := by
    dsimp [s]
    positivity
  have hsLe : s ≤ t := by
    dsimp [s]
    have hdiv :
        t / ((i : Real) + 1) ≤ t / (1 : Real) := by
      have hdenGe : (1 : Real) ≤ (i : Real) + 1 := by
        have hiNonneg : (0 : Real) ≤ (i : Real) := by
          exact_mod_cast Nat.zero_le i
        linarith
      exact div_le_div_of_nonneg_left _ht.le (by norm_num) hdenGe
    simpa using hdiv
  have hcoordBounds :=
    helperForTheorem_25_6_coordinate_bound_from_monotoneComparison_with_endpoint_and_symmetricInteriorPoints
      (f := f) hf (j := j) (hρpos := hρpos) hsPos hsLe (hpairLower i) (hqSeqSub i)
      (hvPlus := by
        simpa [z] using hvPlus j)
      (hvMinus := by
        simpa [z] using hvMinus j)
  have hcoordBounds' :
      vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|) ≤ qSeq i j ∧
        qSeq i j ≤ vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|) := by
    simpa [z, s] using hcoordBounds
  have hUpperAbs :
      |qSeq i j| ≤
        max
          (|vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|)|)
          (|vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|)|) := by
    rcases hcoordBounds' with ⟨hLower, hUpper⟩
    refine abs_le.2 ?_
    constructor
    · have hlowerMax :
          -max
              (|vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|)|)
              (|vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|)|) ≤
            vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|) := by
        have hnegAbs :
            -|vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|)| ≤
              vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|) := by
          exact neg_abs_le _
        have hmaxLe :
            -max
                (|vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|)|)
                (|vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|)|) ≤
              -|vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|)| := by
          exact neg_le_neg (le_max_right _ _)
        exact le_trans hmaxLe hnegAbs
      linarith
    · have hupperMax :
          vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|) ≤
            max
              (|vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|)|)
              (|vMinus j j - (2 / ρ) * t * (|dotProduct u (vMinus j)| + |d|)|) := by
        have hleAbs :
            vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|) ≤
              |vPlus j j + (2 / ρ) * t * (|dotProduct u (vPlus j)| + |d|)| := by
          exact le_abs_self _
        exact le_trans hleAbs (le_max_left _ _)
      linarith
  simpa [M] using hUpperAbs

/-- Helper for Theorem 25.6: once every coordinate of a sequence in `ℝⁿ` stays inside one fixed
box, the whole sequence lies in a common closed ball and therefore has a convergent subsequence. -/
lemma helperForTheorem_25_6_convergent_subseq_of_uniform_coordinate_bounds
    {n : Nat} (qSeq : ℕ → Fin n → Real) {M : Fin n → Real}
    (hMnonneg : ∀ j : Fin n, 0 ≤ M j)
    (hbound : ∀ i : ℕ, ∀ j : Fin n, |qSeq i j| ≤ M j) :
    ∃ φ : ℕ → ℕ, ∃ q : Fin n → Real,
      StrictMono φ ∧
      Filter.Tendsto (fun k : ℕ => qSeq (φ k)) Filter.atTop (nhds q) := by
  let R : Real := ∑ j : Fin n, M j
  have hRnonneg : 0 ≤ R := by
    -- Summing the coordinate radii gives a nonnegative scalar radius.
    exact Finset.sum_nonneg (fun j _ => hMnonneg j)
  have hmem :
      ∀ i : ℕ, qSeq i ∈ Metric.closedBall (0 : Fin n → Real) R := by
    intro i
    have hcoord :
        ∀ j : Fin n, ‖qSeq i j‖ ≤ R := by
      intro j
      have hcoordM : ‖qSeq i j‖ ≤ M j := by
        simpa [Real.norm_eq_abs] using hbound i j
      have hMle : M j ≤ R := by
        show M j ≤ ∑ k : Fin n, M k
        exact
          Finset.single_le_sum
            (fun k _ => hMnonneg k)
            (by simp : j ∈ (Finset.univ : Finset (Fin n)))
      exact le_trans hcoordM hMle
    have hnorm : ‖qSeq i‖ ≤ R := by
      -- In finite dimension, bounding each coordinate bounds the sup norm of the whole vector.
      exact (pi_norm_le_iff_of_nonneg (x := qSeq i) (r := R) hRnonneg).2 hcoord
    simpa [R, Metric.mem_closedBall, dist_eq_norm] using hnorm
  rcases (isCompact_closedBall (0 : Fin n → Real) R).tendsto_subseq hmem with
    ⟨q, _hqBall, φ, hφ, hφTendsto⟩
  -- Compactness of the closed ball supplies the desired convergent subsequence.
  exact ⟨φ, q, hφ, hφTendsto⟩

/-- Helper for Theorem 25.6: along a nonzero admissible ray, the interior support-realizers can
be chosen so that a subsequence converges in `Fin n → Real`. -/
lemma helperForTheorem_25_6_convergent_supportRealizer_subseq_on_admissibleRay
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x u : Fin n → Real} {t : Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hdirNeBot : upperDirectionalDerivativeAt f x u ≠ ⊥)
    (hu0 : u ≠ 0) (ht : 0 < t)
    (hxtuInt : x + t • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∃ qSeq : ℕ → Fin n → Real, ∃ φ : ℕ → ℕ, ∃ q : Fin n → Real,
      (∀ i : ℕ,
        let xi := x + (t / ((i : Real) + 1)) • u
        qSeq i ∈ closure (gradientLimitVectorsAt f xi) ∧
          (((dotProduct (qSeq i) u : Real) : EReal) = upperDirectionalDerivativeAt f xi u)) ∧
      StrictMono φ ∧
      Filter.Tendsto (fun k : ℕ => qSeq (φ k)) Filter.atTop (nhds q) := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let z : Fin n → Real := x + t • u
  let xSeq : ℕ → Fin n → Real := fun i => x + (t / ((i : Real) + 1)) • u
  let c : Real := t / 2
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv : Convex Real domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hfConv
  have hzEq : z = x + t • u := rfl
  have hxSeqInt : ∀ i : ℕ, xSeq i ∈ interior domf := by
    intro i
    let a : Real := 1 / ((i : Real) + 1)
    let b : Real := 1 - a
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hb : 0 ≤ b := by
      dsimp [a, b]
      have hEq : 1 - 1 / ((i : Real) + 1) = (i : Real) / ((i : Real) + 1) := by
        have hden : ((i : Real) + 1) ≠ 0 := by positivity
        field_simp [hden]
        ring
      rw [hEq]
      positivity
    have hab : a + b = 1 := by
      dsimp [a, b]
      ring
    have hcombo :
        a • z + b • x ∈ interior domf :=
      helperForTheorem_25_6_strictConvexCombo_mem_interior_of_mem_effectiveDomain_and_mem_interior
        (f := f) hf hx hxtuInt ha hb hab
    have hxSeqEq : a • z + b • x = xSeq i := by
      ext j
      dsimp [a, b, z, xSeq]
      simp [Pi.add_apply, Pi.smul_apply]
      field_simp
      ring
    exact hxSeqEq.symm ▸ hcombo
  have hxSeqFinite :
      ∀ i : ℕ, f (xSeq i) ≠ ⊤ ∧ f (xSeq i) ≠ ⊥ := by
    intro i
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset (hxSeqInt i)),
        hproper.2.2 (xSeq i) (by simp)⟩
  have hqData :
      ∀ i : ℕ, ∃ q : Fin n → Real,
        q ∈ closure (gradientLimitVectorsAt f (xSeq i)) ∧
          (((dotProduct q u : Real) : EReal) = upperDirectionalDerivativeAt f (xSeq i) u) := by
    intro i
    -- Every interior point on the admissible ray already has an exposed-point support realizer.
    exact
      helperForTheorem_25_6_exists_closureGradientLimitVector_attaining_directionalDerivative_of_mem_interior
        (f := f) hf hf_closed (hxSeqInt i) u
  choose qSeq hqSeqClosure hqSeqPair using hqData
  have hqSeqSub :
      ∀ i : ℕ,
        dotProductEquiv Real (Fin n) (qSeq i) ∈ subdifferentialAt f (xSeq i) := by
    intro i
    -- A closure-gradient witness on an interior fiber is already an actual subgradient there.
    exact
      helperForTheorem_25_6_closureGradientLimitVectors_subset_preimageSubdifferential_of_mem_interior
        (f := f) hf hf_closed (hxSeqInt i) (hqSeqClosure i)
  have hSymmetricComparison :
      ∃ ρ : Real, 0 < ρ ∧
        ∃ vPlus vMinus : Fin n → Fin n → Real,
          (∀ j : Fin n,
            let e : Fin n → Real := Pi.single j (1 : Real)
            z + (ρ / 2) • e ∈ interior domf ∧
              vPlus j ∈
                ((dotProductEquiv Real (Fin n)) ⁻¹'
                  subdifferentialAt f (z + (ρ / 2) • e))) ∧
          (∀ j : Fin n,
            let e : Fin n → Real := Pi.single j (1 : Real)
            z - (ρ / 2) • e ∈ interior domf ∧
              vMinus j ∈
                ((dotProductEquiv Real (Fin n)) ⁻¹'
                  subdifferentialAt f (z - (ρ / 2) • e))) := by
    -- Freeze one interior comparison box around the endpoint `z = x + t • u`.
    simpa [domf, z] using
      helperForTheorem_25_6_exists_symmetricInteriorComparisonSubgradients
        (f := f) hf hxtuInt
  have hCoordinateBox :
      ∃ M : Fin n → Real, ∀ i : ℕ, ∀ j : Fin n, |qSeq i j| ≤ M j := by
    rcases hSymmetricComparison with ⟨ρ, hρpos, _vPlus, _vMinus, hplusInt, hminusInt⟩
    have hplusIntOnly :
        ∀ j : Fin n,
          let e : Fin n → Real := Pi.single j (1 : Real)
          z + (ρ / 2) • e ∈ interior domf := by
      intro j
      exact (hplusInt j).1
    have hminusIntOnly :
        ∀ j : Fin n,
          let e : Fin n → Real := Pi.single j (1 : Real)
          z - (ρ / 2) • e ∈ interior domf := by
      intro j
      exact (hminusInt j).1
    -- One fixed interior center subgradient at `z = x + t • u` plus the secants to
    -- `z ± (ρ / 2) eⱼ` already bound every coordinate of each `qSeq i` by monotonicity.
    simpa [z] using
      helperForTheorem_25_6_uniform_coordinate_bound_on_admissibleRay_from_center_secants
        (f := f) hf hf_closed hx ht hxtuInt hdirNeBot hρpos hplusIntOnly hminusIntOnly
        (qSeq := qSeq) (hqSeqSub := by
          intro i
          simpa [xSeq] using hqSeqSub i)
        (hqSeqPair := by
          intro i
          simpa [xSeq] using (hqSeqPair i).symm)
  rcases hCoordinateBox with ⟨M, hM⟩
  have hMnonneg : ∀ j : Fin n, 0 ≤ M j := by
    intro j
    exact le_trans (abs_nonneg (qSeq 0 j)) (hM 0 j)
  rcases
      helperForTheorem_25_6_convergent_subseq_of_uniform_coordinate_bounds
        (qSeq := qSeq) hMnonneg hM with
    ⟨φ, q, hφ, hφTendsto⟩
  -- Once the common coordinate box is available, compactness finishes the subsequence extraction.
  refine ⟨qSeq, φ, q, ?_, hφ, hφTendsto⟩
  intro i
  exact ⟨hqSeqClosure i, hqSeqPair i⟩

/-- Helper for Theorem 25.6: once the admissible-ray selector converges, every limit pairing still
dominates the boundary directional derivative because each point of the ray gives a positive secant
quotient from `x` that is bounded above by the chosen subgradient pairing. -/
lemma helperForTheorem_25_6_pairing_limit_eq_upperDirectionalDerivative_on_admissibleRay
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x u : Fin n → Real} {t : Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (ht : 0 < t)
    (qSeq : ℕ → Fin n → Real) (φ : ℕ → ℕ) (q : Fin n → Real)
    (_hφ : StrictMono φ)
    (hqSub :
      ∀ i : ℕ,
        let xi := x + (t / ((i : Real) + 1)) • u
        dotProductEquiv Real (Fin n) (qSeq i) ∈ subdifferentialAt f xi)
    (hqTendsto : Filter.Tendsto (fun k : ℕ => qSeq (φ k)) Filter.atTop (nhds q)) :
    upperDirectionalDerivativeAt f x u ≤ (((dotProduct q u : Real) : EReal)) := by
  let xSeq : ℕ → Fin n → Real := fun i => x + (t / ((i : Real) + 1)) • u
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    constructor
    · exact
        mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) hx
    · exact hproper.2.2 x (by simp)
  have hpairTendsto :
      Filter.Tendsto
        (fun k : ℕ => (((dotProduct (qSeq (φ k)) u : Real) : EReal)))
        Filter.atTop (nhds (((dotProduct q u : Real) : EReal))) := by
    -- Continuity of the dot product and of the real embedding into `EReal` transports the vector
    -- convergence to convergence of the scalar pairings.
    have hrealTendsto :
        Filter.Tendsto (fun k : ℕ => dotProduct (qSeq (φ k)) u) Filter.atTop
          (nhds (dotProduct q u)) := by
      simpa [dotProductEquiv_apply_apply, dotProduct_comm] using
        (((dotProductEquiv Real (Fin n) u).continuous_of_finiteDimensional.continuousAt.tendsto).comp
          hqTendsto)
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp hrealTendsto
  have hlowerEach :
      ∀ k : ℕ,
        upperDirectionalDerivativeAt f x u ≤
          (((dotProduct (qSeq (φ k)) u : Real) : EReal)) := by
    intro k
    let i : ℕ := φ k
    let s : Real := t / (((i : ℕ) : Real) + 1)
    let xi : Fin n → Real := xSeq i
    have hsPos : 0 < s := by
      dsimp [s]
      positivity
    have hqSubi :
        dotProductEquiv Real (Fin n) (qSeq i) ∈ subdifferentialAt f xi := by
      simpa [xSeq, xi, s] using hqSub i
    have hxiTop : f xi ≠ (⊤ : EReal) := by
      intro hxiTop
      have hineq := hqSubi x
      rw [hxiTop, EReal.top_add_coe] at hineq
      exact hxFinite.1 (top_le_iff.mp hineq)
    have hxiFinite : f xi ≠ (⊤ : EReal) ∧ f xi ≠ (⊥ : EReal) := by
      exact ⟨hxiTop, hproper.2.2 xi (by simp [xi, xSeq])⟩
    have hsecLe :
        upperDirectionalDerivativeAt f x u ≤ directionalDifferenceQuotientAt f x u s := by
      rcases convex_directionalDerivative_monotone_exists_and_sublinear f hfConv x hxFinite with
        ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
      rcases hdir u with ⟨_hmono, _htend, hsInfEq⟩
      have hQbdd :
          BddBelow ((Set.Ioi (0 : ℝ)).image fun τ : ℝ => directionalDifferenceQuotientAt f x u τ) := by
        refine ⟨⊥, ?_⟩
        intro r hr
        simp at hr ⊢
      rw [hsInfEq]
      exact csInf_le hQbdd ⟨s, hsPos, rfl⟩
    lift f x to Real using hxFinite with xr hxr
    lift f xi to Real using hxiFinite with xir hxi
    have hsubReal : xr ≥ xir + dotProduct (qSeq i) (x - xi) := by
      exact
        EReal.coe_le_coe_iff.mp
          (by simpa [hxr, hxi, dotProductEquiv_apply_apply, EReal.coe_add] using hqSubi x)
    have hdotEq :
        dotProduct (qSeq i) (x - xi) = -s * dotProduct (qSeq i) u := by
      -- Along the admissible ray, the displacement from `xi` back to `x` is exactly `-s • u`.
      calc
        dotProduct (qSeq i) (x - xi) = dotProduct (qSeq i) (-s • u) := by
          congr 1
          ext j
          dsimp [xi, xSeq, s]
          ring
        _ = -s * dotProduct (qSeq i) u := by
          rw [dotProduct_smul]
          simp [smul_eq_mul, mul_comm]
    have hquotReal :
        ((xir - xr) / s) ≤ dotProduct (qSeq i) u := by
      rw [hdotEq] at hsubReal
      have hmul : xir - xr ≤ s * dotProduct (qSeq i) u := by
        nlinarith
      have hmul' : xir - xr ≤ dotProduct (qSeq i) u * s := by
        simpa [mul_comm] using hmul
      exact (div_le_iff₀ hsPos).2 hmul'
    have hdqEq :
        directionalDifferenceQuotientAt f x u s = (((xir - xr) / s : Real) : EReal) := by
      have hstep : x + s • u = xi := by
        rfl
      simp [directionalDifferenceQuotientAt, hstep, hxr, hxi, div_eq_mul_inv, EReal.coe_inv]
    have hquotLe :
        directionalDifferenceQuotientAt f x u s ≤
          (((dotProduct (qSeq i) u : Real) : EReal)) := by
      simpa [hdqEq] using
        (show (((xir - xr) / s : Real) : EReal) ≤ (((dotProduct (qSeq i) u : Real) : EReal)) by
          exact_mod_cast hquotReal)
    exact le_trans hsecLe hquotLe
  -- The closed half-line `{r | f'(x;u) ≤ r}` absorbs the convergent pairing subsequence.
  exact
    isClosed_Ici.mem_of_tendsto hpairTendsto (Filter.Eventually.of_forall hlowerEach)

/-- Helper for Theorem 25.6: along an admissible direction, either the upper directional
derivative is `⊥`, or it is realized by a point of `closure (gradientLimitVectorsAt f x)`. -/
lemma helperForTheorem_25_6_admissibleDirectionalDerivative_eq_bot_or_exists_closureGradientLimitVector
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x u : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hu : ∃ t : Real, 0 < t ∧
      x + t • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    upperDirectionalDerivativeAt f x u = ⊥ ∨
      ∃ q : Fin n → Real,
        q ∈ closure (gradientLimitVectorsAt f x) ∧
          (((dotProduct q u : Real) : EReal) = upperDirectionalDerivativeAt f x u) := by
  rcases hu with ⟨t, ht, hxtuInt⟩
  by_cases hu0 : u = 0
  · subst hu0
    -- The zero-direction case is already an interior problem, because the ray hypothesis says `x ∈ int(dom f)`.
    have hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      simpa using hxtuInt
    -- Interior directional derivatives are realized by the already-proved interior theorem.
    right
    simpa using
      helperForTheorem_25_6_exists_closureGradientLimitVector_attaining_directionalDerivative_of_mem_interior
        (f := f) hf hf_closed hxInt (0 : Fin n → Real)
  · by_cases hbot : upperDirectionalDerivativeAt f x u = ⊥
    · -- On the `⊥` branch there is no real-valued pairing to realize, so this is the correct stop.
      exact Or.inl hbot
    · right
      have hxSeqTendsto :
        Filter.Tendsto
          (fun i : ℕ => x + (t / ((i : Real) + 1)) • u)
          Filter.atTop (nhds x) := by
        have hInvTendsto :
          Filter.Tendsto (fun i : ℕ => (((i : Real) + 1)⁻¹)) Filter.atTop (nhds 0) := by
          simpa [Function.comp, one_mul] using
          (tendsto_mul_add_inv_atTop_nhds_zero (1 : Real) 1 one_ne_zero).comp
            tendsto_natCast_atTop_atTop
        have hScaleTendsto :
          Filter.Tendsto (fun i : ℕ => t / ((i : Real) + 1)) Filter.atTop (nhds 0) := by
          have hMul :
            Filter.Tendsto (fun i : ℕ => t * (((i : Real) + 1)⁻¹))
              Filter.atTop (nhds 0) := by
            simpa using
            (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => t) Filter.atTop (nhds t)).mul
              hInvTendsto
          simpa [div_eq_mul_inv] using hMul
        have hContSmul : Continuous fun s : Real => s • u := by
          fun_prop
        have hSmul :
          Filter.Tendsto (fun i : ℕ => (t / ((i : Real) + 1)) • u)
            Filter.atTop (nhds (0 : Fin n → Real)) := by
          simpa using hContSmul.continuousAt.tendsto.comp hScaleTendsto
        simpa using tendsto_const_nhds.add hSmul
      rcases
        helperForTheorem_25_6_convergent_supportRealizer_subseq_on_admissibleRay
          (f := f) hf hf_closed hx hbot hu0 ht hxtuInt with
        ⟨qSeq, φ, q, hqData, hφ, hqTendsto⟩
      have hxSubseqTendsto :
        Filter.Tendsto
          (fun k : ℕ => x + (t / (((φ k : ℕ) : Real) + 1)) • u)
          Filter.atTop (nhds x) :=
        hxSeqTendsto.comp hφ.tendsto_atTop
      have hqClosure :
        q ∈ closure (gradientLimitVectorsAt f x) := by
        -- The diagonal transport lemma moves the convergent interior witness family back to the
        -- boundary fiber at `x`.
        exact
        helperForTheorem_25_6_limit_of_closureGradientLimitVectors_mem_closureGradientLimitVectors
          (f := f)
          (xSeq := fun k : ℕ => x + (t / (((φ k : ℕ) : Real) + 1)) • u)
          (qSeq := fun k : ℕ => qSeq (φ k))
          hxSubseqTendsto hqTendsto
          (fun k : ℕ => by
            simpa using (hqData (φ k)).1)
      have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
        helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
      have hfConv : ConvexFunction f := by
        simpa [ConvexFunction] using hproper.1
      have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
        constructor
        · exact
            mem_effectiveDomain_imp_ne_top
              (S := (Set.univ : Set (Fin n → Real))) (f := f) hx
        · exact hproper.2.2 x (by simp)
      have hqSubAtX :
        dotProductEquiv Real (Fin n) q ∈ subdifferentialAt f x := by
        exact
        helperForTheorem_25_6_closureGradientLimitVectors_subset_preimageSubdifferential_of_mem_effectiveDomain
          (f := f) hf hf_closed hx hqClosure
      have hqUpper :
        (((dotProduct q u : Real) : EReal)) ≤ upperDirectionalDerivativeAt f x u := by
        -- The transported limit point is already a true subgradient at `x`, so its pairing is
        -- bounded above by the directional derivative there.
        have hminorant :=
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          f hfConv x hxFinite (dotProductEquiv Real (Fin n) q)).1.1 hqSubAtX
        simpa [dotProductEquiv_apply_apply] using hminorant u
      have hqLower :
        upperDirectionalDerivativeAt f x u ≤ (((dotProduct q u : Real) : EReal)) := by
        -- Rockafellar's admissible-ray comparison gives the missing lower inequality by taking
        -- secant quotients from `x` along the ray and then passing to the subsequential limit.
        have hxSeqInt :
          ∀ i : ℕ,
            x + (t / ((i : Real) + 1)) • u ∈
              interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
          intro i
          let a : Real := 1 / ((i : Real) + 1)
          let b : Real := 1 - a
          have ha : 0 < a := by
            dsimp [a]
            positivity
          have hb : 0 ≤ b := by
            dsimp [a, b]
            have hEq : 1 - 1 / ((i : Real) + 1) = (i : Real) / ((i : Real) + 1) := by
              have hden : ((i : Real) + 1) ≠ 0 := by positivity
              field_simp [hden]
              ring
            rw [hEq]
            positivity
          have hab : a + b = 1 := by
            dsimp [a, b]
            ring
          have hcombo :
            a • (x + t • u) + b • x ∈
              interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
            helperForTheorem_25_6_strictConvexCombo_mem_interior_of_mem_effectiveDomain_and_mem_interior
              (f := f) hf hx hxtuInt ha hb hab
          have hxSeqEq :
            a • (x + t • u) + b • x = x + (t / ((i : Real) + 1)) • u := by
            ext j
            dsimp [a, b]
            ring
          exact hxSeqEq.symm ▸ hcombo
        exact
        helperForTheorem_25_6_pairing_limit_eq_upperDirectionalDerivative_on_admissibleRay
          (f := f) hf hx ht qSeq φ q hφ
          (fun i : ℕ => by
            have hsubAtXi :
                dotProductEquiv Real (Fin n) (qSeq i) ∈
                  subdifferentialAt f (x + (t / ((i : Real) + 1)) • u) := by
              exact
                helperForTheorem_25_6_closureGradientLimitVectors_subset_preimageSubdifferential_of_mem_interior
                  (f := f) hf hf_closed (hxSeqInt i) (hqData i).1
            simpa using hsubAtXi)
            hqTendsto
      refine ⟨q, hqClosure, ?_⟩
      exact le_antisymm hqUpper hqLower

/-- Helper for Theorem 25.6: once an admissible direction is realized by a point of
`closure (gradientLimitVectorsAt f x)`, the support of `cl (conv S(x))` dominates the directional
derivative in that direction. -/
lemma helperForTheorem_25_6_upperDirectionalDerivative_le_support_closureConvexHull_gradientLimitVectors_of_mem_admissibleDirection
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x u : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hu : ∃ t : Real, 0 < t ∧
      x + t • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    upperDirectionalDerivativeAt f x u ≤
      supportFunctionEReal (closure (convexHull Real (gradientLimitVectorsAt f x))) u := by
  let A : Set (Fin n → Real) := closure (convexHull Real (gradientLimitVectorsAt f x))
  have hdir :=
    helperForTheorem_25_6_admissibleDirectionalDerivative_eq_bot_or_exists_closureGradientLimitVector
      (f := f) hf hf_closed hx hu
  rcases hdir with hbot | hrealizer
  · -- If the directional derivative is `⊥`, the support domination is automatic.
    simpa [hbot] using (bot_le : (⊥ : EReal) ≤ supportFunctionEReal A u)
  · rcases hrealizer with ⟨q, hqClosure, hqEq⟩
    have hqMemA : q ∈ A := by
      -- Passing from `closure S(x)` to `cl (conv S(x))` only uses `S(x) ⊆ conv S(x)`.
      exact
        closure_minimal
          (Set.Subset.trans
            (subset_convexHull Real (gradientLimitVectorsAt f x))
            subset_closure)
          isClosed_closure hqClosure
    have hqLe :
        (((dotProduct q u : Real) : EReal)) ≤ supportFunctionEReal A u := by
      -- Any specific point of `A` contributes a lower bound to its support function.
      rw [supportFunctionEReal]
      exact le_sSup ⟨q, hqMemA, rfl⟩
    -- Rewrite the realized pairing as the directional derivative.
    calc
      upperDirectionalDerivativeAt f x u = (((dotProduct q u : Real) : EReal)) := by
        symm
        exact hqEq
      _ ≤ supportFunctionEReal A u := hqLe

/-- Helper for Theorem 25.6: if a set has support function never equal to `⊤`, then it is bounded;
the empty-set case is harmless and the nonempty case reduces to Chapter 13. -/
lemma helperForTheorem_25_6_isBounded_of_supportFunctionEReal_ne_top
    {n : Nat} {C : Set (Fin n → Real)}
    (hTop : ∀ y : Fin n → Real, supportFunctionEReal C y ≠ (⊤ : EReal)) :
    Bornology.IsBounded C := by
  by_cases hCne : Set.Nonempty C
  · -- On nonempty sets, Chapter 13 upgrades `≠ ⊤` to boundedness using the automatic `≠ ⊥`.
    refine section13_isBounded_of_supportFunctionEReal_finite ?_
    intro y
    exact ⟨hTop y, section13_supportFunctionEReal_ne_bot_of_nonempty hCne y⟩
  · -- If the set is empty, boundedness is immediate.
    have hCempty : C = ∅ := by
      ext z
      by_cases hz : z ∈ C
      · exact False.elim (hCne ⟨z, hz⟩)
      · simp [hz]
    simpa [hCempty] using (Bornology.isBounded_empty : Bornology.IsBounded (∅ : Set (Fin n → Real)))

/-- Helper for Theorem 25.6: if `closure (S(x))` is bounded, then `closure (conv S(x))` is still
bounded, so its support function is finite in every direction. -/
lemma helperForTheorem_25_6_supportFunctionEReal_ne_top_of_bounded_closureGradientLimitVectors
    {n : Nat} (f : (Fin n → Real) → EReal)
    {x : Fin n → Real}
    (hBdd : Bornology.IsBounded (closure (gradientLimitVectorsAt f x))) :
    ∀ y : Fin n → Real,
      supportFunctionEReal (closure (convexHull Real (gradientLimitVectorsAt f x))) y ≠ ⊤ := by
  let S : Set (Fin n → Real) := gradientLimitVectorsAt f x
  have hSbdd : Bornology.IsBounded S := hBdd.subset subset_closure
  have hHullBdd : Bornology.IsBounded (convexHull Real S) := by
    -- Convex hulls preserve boundedness in finite-dimensional normed spaces.
    simpa using (isBounded_convexHull (s := S)).2 hSbdd
  have hClosedHullBdd : Bornology.IsBounded (closure (convexHull Real S)) := hHullBdd.closure
  intro y
  -- The Chapter 13 support-function criterion applies once the hull is known bounded.
  exact
    section13_supportFunctionEReal_ne_top_of_isBounded
      (C := closure (convexHull Real S)) hClosedHullBdd y

/-- Helper for Theorem 25.6: a coordinate box cut out by finitely many inequalities
`|q j| ≤ M j` is closed in `ℝⁿ`. -/
lemma helperForTheorem_25_6_isClosed_coordinateBox
    {n : Nat} (M : Fin n → Real) :
    IsClosed {q : Fin n → Real | ∀ j : Fin n, |q j| ≤ M j} := by
  classical
  -- The box is a finite intersection of closed coordinate slabs.
  simp_rw [show ({q : Fin n → Real | ∀ j : Fin n, |q j| ≤ M j} : Set (Fin n → Real)) =
      ⋂ j : Fin n, {q : Fin n → Real | |q j| ≤ M j} by
      ext q
      simp]
  refine isClosed_iInter ?_
  intro j
  exact isClosed_le ((continuous_apply j).abs) continuous_const

/-- Helper for Theorem 25.6: every finite coordinate box in `ℝⁿ` is bounded. -/
lemma helperForTheorem_25_6_isBounded_coordinateBox
    {n : Nat} (M : Fin n → Real) :
    Bornology.IsBounded {q : Fin n → Real | ∀ j : Fin n, |q j| ≤ M j} := by
  let R : Real := ∑ j : Fin n, |M j|
  have hR : 0 ≤ R := by
    exact Finset.sum_nonneg (fun j _ => abs_nonneg (M j))
  have hsubset :
      {q : Fin n → Real | ∀ j : Fin n, |q j| ≤ M j} ⊆
        Metric.closedBall (0 : Fin n → Real) R := by
    intro q hq
    rw [Metric.mem_closedBall, dist_eq_norm]
    -- Bounding each coordinate by `|M j|` places the whole vector in one closed ball.
    simpa using
      (pi_norm_le_iff_of_nonneg (x := q) (r := R) hR).2 (by
        intro j
        have hqj : |q j| ≤ M j := hq j
        have hMj : |M j| ≤ R := by
          simp [R]
          exact Finset.single_le_sum (fun k _ => abs_nonneg (M k)) (by simp)
        exact le_trans (le_trans hqj (le_abs_self (M j))) hMj)
  exact (Metric.isBounded_closedBall (x := (0 : Fin n → Real)) (r := R)).subset hsubset

/-- Helper for Theorem 25.6: eventual membership in a closed coordinate box survives passage to
the limit. -/
lemma helperForTheorem_25_6_mem_coordinateBox_of_tendsto_eventually
    {n : Nat} {q : Fin n → Real} {qSeq : ℕ → Fin n → Real} {M : Fin n → Real}
    (hq : Filter.Tendsto qSeq Filter.atTop (nhds q))
    (hEventually :
      ∀ᶠ i in Filter.atTop, qSeq i ∈ {p : Fin n → Real | ∀ j : Fin n, |p j| ≤ M j}) :
    ∀ j : Fin n, |q j| ≤ M j := by
  have hClosed :
      IsClosed {p : Fin n → Real | ∀ j : Fin n, |p j| ≤ M j} :=
    helperForTheorem_25_6_isClosed_coordinateBox (M := M)
  -- Closedness of the coordinate box lets the limit inherit the same bounds.
  exact hClosed.mem_of_tendsto hq hEventually

/-- Helper for Theorem 25.6: once a boundary subgradient has one absolute longitudinal pairing
bound against a fixed interior center, the symmetric comparison subgradients around that center
bound each coordinate. -/
lemma helperForTheorem_25_6_coordinate_bound_from_abs_longitudinalPairing_at_boundary_and_symmetricInteriorPoints
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x z q vPlus vMinus : Fin n → Real} {ρ B : Real} {j : Fin n}
    (hρpos : 0 < ρ)
    (hqPairAbs : |dotProduct (z - x) q| ≤ B)
    (hqSub :
      q ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x))
    (hvPlus :
      let e : Fin n → Real := Pi.single j (1 : Real)
      vPlus ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          subdifferentialAt f (z + (ρ / 2) • e)))
    (hvMinus :
      let e : Fin n → Real := Pi.single j (1 : Real)
      vMinus ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          subdifferentialAt f (z - (ρ / 2) • e))) :
    let BPlus := (2 / ρ) * (|dotProduct (z - x) vPlus| + B)
    let BMinus := (2 / ρ) * (|dotProduct (z - x) vMinus| + B)
    vMinus j - BMinus ≤ q j ∧ q j ≤ vPlus j + BPlus := by
  let e : Fin n → Real := Pi.single j (1 : Real)
  let BPlus : Real := (2 / ρ) * (|dotProduct (z - x) vPlus| + B)
  let BMinus : Real := (2 / ρ) * (|dotProduct (z - x) vMinus| + B)
  have hρhalfPos : 0 < ρ / 2 := by
    positivity
  have hBnonneg : 0 ≤ B := by
    exact le_trans (abs_nonneg (dotProduct (z - x) q)) hqPairAbs
  have hvPlus' :
      vPlus ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          subdifferentialAt f (z + (ρ / 2) • e)) := by
    simpa [e] using hvPlus
  have hvMinus' :
      vMinus ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          subdifferentialAt f (z - (ρ / 2) • e)) := by
    simpa [e] using hvMinus
  have hmonoPlus :=
    helperForTheorem_25_6_preimageSubdifferential_monotone
      (f := f) hf hqSub hvPlus'
  have hmonoMinus :=
    helperForTheorem_25_6_preimageSubdifferential_monotone
      (f := f) hf hqSub hvMinus'
  have hplusRewrite :
      0 ≤ dotProduct (z - x) (vPlus - q) + (ρ / 2) * (vPlus j - q j) := by
    have hdisp :
        z + (ρ / 2) • e - x = (z - x) + (ρ / 2) • e := by
      ext k
      by_cases hk : k = j
      · subst hk
        simp [e]
        ring
      · simp [e, hk]
    calc
      0 ≤ dotProduct ((z - x) + (ρ / 2) • e) (vPlus - q) := by
        simpa [hdisp] using hmonoPlus
      _ = dotProduct (z - x) (vPlus - q) + (ρ / 2) * (vPlus j - q j) := by
        simp [e, dotProduct_add, smul_dotProduct, sub_eq_add_neg]
        ring
  have hminusRewrite :
      0 ≤ dotProduct (z - x) (vMinus - q) - (ρ / 2) * (vMinus j - q j) := by
    have hdisp :
        z - (ρ / 2) • e - x = (z - x) - (ρ / 2) • e := by
      ext k
      by_cases hk : k = j
      · subst hk
        simp [e]
        ring
      · simp [e, hk]
    calc
      0 ≤ dotProduct ((z - x) - (ρ / 2) • e) (vMinus - q) := by
        simpa [hdisp] using hmonoMinus
      _ = dotProduct (z - x) (vMinus - q) - (ρ / 2) * (vMinus j - q j) := by
        simp [e, smul_dotProduct, sub_eq_add_neg]
        ring
  have hpairLower : -B ≤ dotProduct (z - x) q := by
    have hpairBounds :
        -B ≤ dotProduct (z - x) q ∧ dotProduct (z - x) q ≤ B := by
      simpa [abs_le] using hqPairAbs
    exact hpairBounds.1
  have hplusTermBound :
      dotProduct (z - x) (vPlus - q) ≤ |dotProduct (z - x) vPlus| + B := by
    have hvPlusAbs : dotProduct (z - x) vPlus ≤ |dotProduct (z - x) vPlus| := le_abs_self _
    have hraw :
        dotProduct (z - x) vPlus - dotProduct (z - x) q ≤
          |dotProduct (z - x) vPlus| + B := by
      linarith
    simpa [dotProduct_sub] using hraw
  have hminusTermBound :
      dotProduct (z - x) (vMinus - q) ≤ |dotProduct (z - x) vMinus| + B := by
    have hvMinusAbs : dotProduct (z - x) vMinus ≤ |dotProduct (z - x) vMinus| := le_abs_self _
    have hraw :
        dotProduct (z - x) vMinus - dotProduct (z - x) q ≤
          |dotProduct (z - x) vMinus| + B := by
      linarith
    simpa [dotProduct_sub] using hraw
  have hupperScaled :
      (ρ / 2) * (q j - vPlus j) ≤ |dotProduct (z - x) vPlus| + B := by
    linarith
  have hlowerScaled :
      (ρ / 2) * (vMinus j - q j) ≤ |dotProduct (z - x) vMinus| + B := by
    linarith
  have hupper :
      q j ≤ vPlus j + BPlus := by
    have hdiv :
        q j - vPlus j ≤ (|dotProduct (z - x) vPlus| + B) / (ρ / 2) := by
      exact (le_div_iff₀ hρhalfPos).2 (by simpa [mul_comm] using hupperScaled)
    have hdiv' :
        q j - vPlus j ≤ BPlus := by
      simpa [BPlus, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    linarith
  have hlower :
      vMinus j - BMinus ≤ q j := by
    have hdiv :
        vMinus j - q j ≤ (|dotProduct (z - x) vMinus| + B) / (ρ / 2) := by
      exact (le_div_iff₀ hρhalfPos).2 (by simpa [mul_comm] using hlowerScaled)
    have hdiv' :
        vMinus j - q j ≤ BMinus := by
      simpa [BMinus, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    linarith
  exact ⟨hlower, hupper⟩

/-- Helper for Theorem 25.6: transporting a boundary gradient-limit vector into the subdifferential
at `x` and comparing it with a fixed interior subgradient at `z` yields only a one-sided
longitudinal pairing bound. -/
lemma helperForTheorem_25_6_monotonicity_gives_only_upper_longitudinal_bound
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x z g v : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hg : g ∈ gradientLimitVectorsAt f x)
    (hv :
      v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f z)) :
    dotProduct (z - x) g ≤ dotProduct (z - x) v := by
  -- First move the gradient-limit witness into the boundary subdifferential at `x`.
  have hgSub :
      g ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
    exact
      helperForTheorem_25_6_closureGradientLimitVectors_subset_preimageSubdifferential_of_mem_effectiveDomain
        (f := f) hf hf_closed hx (subset_closure hg)
  -- Then apply monotonicity between the subgradients at `x` and `z`.
  have hmono :
      0 ≤ dotProduct (z - x) (v - g) :=
    helperForTheorem_25_6_preimageSubdifferential_monotone
      (f := f) hf hgSub hv
  -- Rewriting the pairing of a difference isolates the target term.
  have hmono' :
      0 ≤ dotProduct (z - x) v - dotProduct (z - x) g := by
    simpa [dotProduct_sub] using hmono
  linarith

/-
Rockafellar's proof of Theorem 25.6 proceeds from the admissible-ray argument developed here to
the Chapter 18 extreme-point / extreme-direction decomposition used in the later files; it does not
introduce a separate boundary boundedness lemma for `S(x)` or for `cl (conv S(x))`.
-/

/-- Helper for Theorem 25.6: after vectorizing the normal cone to `dom f`, its support function is
the indicator of the raw polar inequality set. -/
lemma helperForTheorem_25_6_support_preimageNormalCone_eq_indicatorPolar
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    let K : Set (Fin n → Real) :=
      ((dotProductEquiv Real (Fin n)) ⁻¹'
        normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x)
    supportFunctionEReal K =
      indicatorFunction {y : Fin n → Real | ∀ v ∈ K, dotProduct v y ≤ 0} := by
  intro K
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv : Convex Real domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hfConv
  let Kcone : ConvexCone ℝ (Fin n → Real) :=
    { carrier := K
      smul_mem' := by
        intro c hc v hv
        rw [Set.mem_preimage] at hv ⊢
        refine (mem_normalConeAt_iff).2 ?_
        rcases (mem_normalConeAt_iff.1 hv) with ⟨hxDom, hvIneq⟩
        constructor
        · exact hxDom
        · intro z hz
          have hvScaled :
              c * dotProduct v (z - x) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) (hvIneq z hz)
          simpa [dotProductEquiv_apply_apply, dotProduct_smul, smul_eq_mul,
            mul_comm, mul_left_comm, mul_assoc] using hvScaled
      add_mem' := by
        intro u hu v hv
        rw [Set.mem_preimage] at hu hv ⊢
        refine (mem_normalConeAt_iff).2 ?_
        rcases (mem_normalConeAt_iff.1 hu) with ⟨hxDom, huIneq⟩
        rcases (mem_normalConeAt_iff.1 hv) with ⟨_hxDom', hvIneq⟩
        constructor
        · exact hxDom
        · intro z hz
          have hsum :
              dotProduct u (z - x) + dotProduct v (z - x) ≤ 0 :=
            add_nonpos (huIneq z hz) (hvIneq z hz)
          simpa [dotProductEquiv_apply_apply, dotProduct_add] using hsum }
  have hKne : (K : Set (Fin n → Real)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Set.mem_preimage]
    refine (mem_normalConeAt_iff).2 ?_
    constructor
    · simpa [domf] using hx
    · intro z hz
      -- The zero covector satisfies the normal inequality trivially.
      simp
  -- Package the normal-cone support term as an indicator function on the vector polar.
  simpa [K, Kcone] using
    section16_supportFunctionEReal_convexCone_eq_indicatorFunction_polar
      (K := Kcone) hKne


end Section25
end Chap05
