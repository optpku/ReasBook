/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.Certificate

@[expose] public section

open scoped BigOperators

namespace ADMM.ConvergenceProof

open ADMM.FiniteMemory

noncomputable section

/-- The quadratic storage of a vector history is the sum of the scalar
quadratic storages of its coordinates. -/
def coordinateQuadraticStorage {m ℓ : ℕ}
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → Fin m → ℝ) : ℝ :=
  ∑ a : Fin m, quadraticStorage P (fun i ↦ Z i a)

/-- The supply of a vector history is the sum of the scalar supplies of its
coordinates. -/
def coordinateSupply {m ℓ : ℕ} (gamma omega epsilon : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (Z : (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ) : ℝ :=
  ∑ a : Fin m,
    supply gamma omega epsilon lagMinus lagPlus (fun i ↦ Z i a)

/-- Directed certificate weights convert objective-value differences into the
signed lag coefficients when the interpolation origin has value zero. -/
theorem certificateValueFlow {ℓ : ℕ} {gamma : ℝ} (c : Certificate ℓ gamma)
    (Φ : Block → Option (Fin ℓ) → ℝ) (hΦzero : ∀ b, Φ b none = 0) :
    (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
      (c.μ b i j : ℝ) * (Φ b i - Φ b j)) =
      ∑ b : Block, ∑ j : Fin ℓ,
        lagCoefficient c.lagMinus c.lagPlus b j * Φ b (some j) := by
  classical
  -- Reindex the incoming part of the directed sum so that each value is
  -- multiplied by its outgoing-minus-incoming coefficient.
  apply Finset.sum_congr rfl
  intro b hb
  have hcollect :
      (∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          (c.μ b i j : ℝ) * (Φ b i - Φ b j)) =
        ∑ i : Option (Fin ℓ),
          ((∑ j : Option (Fin ℓ), (c.μ b i j : ℝ)) -
            ∑ j : Option (Fin ℓ), (c.μ b j i : ℝ)) * Φ b i := by
    have hincoming :
        (∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            (c.μ b i j : ℝ) * Φ b j) =
          ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            (c.μ b j i : ℝ) * Φ b i := by
      rw [Finset.sum_comm]
    calc
      (∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          (c.μ b i j : ℝ) * (Φ b i - Φ b j)) =
          (∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            (c.μ b i j : ℝ) * Φ b i) -
          ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            (c.μ b i j : ℝ) * Φ b j := by
              simp only [mul_sub, Finset.sum_sub_distrib]
      _ = (∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            (c.μ b i j : ℝ) * Φ b i) -
          ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            (c.μ b j i : ℝ) * Φ b i := by rw [hincoming]
      _ = ∑ i : Option (Fin ℓ),
          ((∑ j : Option (Fin ℓ), (c.μ b i j : ℝ)) -
            ∑ j : Option (Fin ℓ), (c.μ b j i : ℝ)) * Φ b i := by
              simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hcollect, Fintype.sum_option, hΦzero b, mul_zero, zero_add]
  -- The certificate balance identity supplies every remaining generated
  -- coefficient with the required lag coefficient.
  apply Finset.sum_congr rfl
  intro j hj
  rw [c.value_balance b j]

/-- Weighted differences from the current value to every lag telescope to the
signed lag-coefficient pairing of consecutive values. -/
theorem lagValueTelescoping {ℓ : ℕ}
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (Φ : Block → Fin (ℓ + 1) → ℝ) :
    (∑ b : Block, ∑ d : Fin ℓ,
      ((lagMinus b d : ℝ) * (Φ b 0 - Φ b d.succ) +
        (lagPlus b d : ℝ) * (Φ b d.succ - Φ b 0))) =
      ∑ b : Block, ∑ j : Fin ℓ,
        lagCoefficient lagMinus lagPlus b j *
          (Φ b j.castSucc - Φ b j.succ) := by
  classical
  apply Finset.sum_congr rfl
  intro b hb
  -- Each current-to-lag difference is the prefix sum of consecutive
  -- differences, written over `univ` so the triangular sums can commute.
  have hprefix (d : Fin ℓ) :
      Φ b 0 - Φ b d.succ =
        ∑ j : Fin ℓ,
          if j ≤ d then Φ b j.castSucc - Φ b j.succ else 0 := by
    have htelescope := Fin.sum_Iic_sub d (Φ b)
    calc
      Φ b 0 - Φ b d.succ = -(Φ b d.succ - Φ b 0) := by ring
      _ = -∑ j ∈ Finset.Iic d, (Φ b j.succ - Φ b j.castSucc) := by
        rw [htelescope]
      _ = ∑ j ∈ Finset.Iic d, (Φ b j.castSucc - Φ b j.succ) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ j : Fin ℓ,
          if j ≤ d then Φ b j.castSucc - Φ b j.succ else 0 := by
        rw [← Finset.sum_filter]
        congr 1
        ext j
        simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbackward (d : Fin ℓ) :
      Φ b d.succ - Φ b 0 =
        -∑ j : Fin ℓ,
          if j ≤ d then Φ b j.castSucc - Φ b j.succ else 0 := by
    -- Reverse the prefix identity for the opposite lag orientation.
    rw [← hprefix d]
    ring
  simp_rw [hprefix, hbackward]
  simp only [lagCoefficient_apply]
  calc
    (∑ d : Fin ℓ,
        ((lagMinus b d : ℝ) *
            (∑ j : Fin ℓ,
              if j ≤ d then Φ b j.castSucc - Φ b j.succ else 0) +
          (lagPlus b d : ℝ) *
            -(∑ j : Fin ℓ,
              if j ≤ d then Φ b j.castSucc - Φ b j.succ else 0))) =
        ∑ d : Fin ℓ,
          ((lagMinus b d : ℝ) - lagPlus b d) *
            ∑ j : Fin ℓ,
              if j ≤ d then Φ b j.castSucc - Φ b j.succ else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∑ d : Fin ℓ, ∑ j : Fin ℓ,
        if j ≤ d then
          ((lagMinus b d : ℝ) - lagPlus b d) *
            (Φ b j.castSucc - Φ b j.succ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjd : j ≤ d
      · simp only [hjd, if_true]
      · simp only [hjd, if_false, mul_zero]
    _ = ∑ j : Fin ℓ, ∑ d : Fin ℓ,
        if j ≤ d then
          ((lagMinus b d : ℝ) - lagPlus b d) *
            (Φ b j.castSucc - Φ b j.succ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin ℓ,
        (∑ d : Fin ℓ,
          if j ≤ d then (lagMinus b d : ℝ) - lagPlus b d else 0) *
            (Φ b j.castSucc - Φ b j.succ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hjd : j ≤ d
      · simp only [hjd, if_true]
      · simp only [hjd, if_false, zero_mul]

/-- Coordinatewise finite-memory supply separates into vector pairings, the
squared residual coordinates, and the two weighted lag pairings. -/
theorem coordinateSupply_apply {m ℓ : ℕ} (gamma omega epsilon : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (Z : (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ) :
    coordinateSupply gamma omega epsilon lagMinus lagPlus Z =
      omega *
          ((∑ a : Fin m,
              graphNormal gamma .F (fun i ↦ Z i a) 0 *
                graphPosition .F (fun i ↦ Z i a) 0) +
            ∑ a : Fin m,
              graphNormal gamma .J (fun i ↦ Z i a) 0 *
                graphPosition .J (fun i ↦ Z i a) 0) +
        epsilon * ∑ a : Fin m, residual (fun i ↦ Z i a) 0 ^ 2 +
        ∑ b : Block, ∑ d : Fin ℓ,
          ((lagMinus b d : ℝ) *
              ∑ a : Fin m,
                graphNormal gamma b (fun i ↦ Z i a) 0 *
                  (graphPosition b (fun i ↦ Z i a) 0 -
                    graphPosition b (fun i ↦ Z i a) d.succ) +
            (lagPlus b d : ℝ) *
              ∑ a : Fin m,
                graphNormal gamma b (fun i ↦ Z i a) d.succ *
                  (graphPosition b (fun i ↦ Z i a) d.succ -
                    graphPosition b (fun i ↦ Z i a) 0)) := by
  classical
  -- Expand the scalar supply in every coordinate; scalar inner products and
  -- norms reduce to multiplication and squares.
  rw [coordinateSupply]
  simp_rw [supply_apply]
  simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sq_abs]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsumComm (F : Fin m → Block → Fin ℓ → ℝ) :
      (∑ a : Fin m, ∑ b : Block, ∑ d : Fin ℓ, F a b d) =
        ∑ b : Block, ∑ d : Fin ℓ, ∑ a : Fin m, F a b d := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
  rw [hsumComm (fun a b d ↦
      (lagMinus b d : ℝ) *
        ((graphPosition b (fun i ↦ Z i a) 0 -
            graphPosition b (fun i ↦ Z i a) d.succ) *
          graphNormal gamma b (fun i ↦ Z i a) 0)),
    hsumComm (fun a b d ↦
      (lagPlus b d : ℝ) *
        ((graphPosition b (fun i ↦ Z i a) d.succ -
            graphPosition b (fun i ↦ Z i a) 0) *
          graphNormal gamma b (fun i ↦ Z i a) d.succ))]
  simp only [Finset.mul_sum]
  have hcurrentF :
      (∑ a : Fin m,
          omega * (graphPosition .F (fun i ↦ Z i a) 0 *
            graphNormal gamma .F (fun i ↦ Z i a) 0)) =
        ∑ a : Fin m,
          omega * (graphNormal gamma .F (fun i ↦ Z i a) 0 *
            graphPosition .F (fun i ↦ Z i a) 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hcurrentJ :
      (∑ a : Fin m,
          omega * (graphPosition .J (fun i ↦ Z i a) 0 *
            graphNormal gamma .J (fun i ↦ Z i a) 0)) =
        ∑ a : Fin m,
          omega * (graphNormal gamma .J (fun i ↦ Z i a) 0 *
            graphPosition .J (fun i ↦ Z i a) 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hlagMinus :
      (∑ b : Block, ∑ d : Fin ℓ, ∑ a : Fin m,
          (lagMinus b d : ℝ) *
            ((graphPosition b (fun i ↦ Z i a) 0 -
                graphPosition b (fun i ↦ Z i a) d.succ) *
              graphNormal gamma b (fun i ↦ Z i a) 0)) =
        ∑ b : Block, ∑ d : Fin ℓ, ∑ a : Fin m,
          (lagMinus b d : ℝ) *
            (graphNormal gamma b (fun i ↦ Z i a) 0 *
              (graphPosition b (fun i ↦ Z i a) 0 -
                graphPosition b (fun i ↦ Z i a) d.succ)) := by
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hlagPlus :
      (∑ b : Block, ∑ d : Fin ℓ, ∑ a : Fin m,
          (lagPlus b d : ℝ) *
            ((graphPosition b (fun i ↦ Z i a) d.succ -
                graphPosition b (fun i ↦ Z i a) 0) *
              graphNormal gamma b (fun i ↦ Z i a) d.succ)) =
        ∑ b : Block, ∑ d : Fin ℓ, ∑ a : Fin m,
          (lagPlus b d : ℝ) *
            (graphNormal gamma b (fun i ↦ Z i a) d.succ *
              (graphPosition b (fun i ↦ Z i a) d.succ -
                graphPosition b (fun i ↦ Z i a) 0)) := by
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hcurrentF, hcurrentJ, hlagMinus, hlagPlus]

/-- A positive-semidefinite scalar matrix remains nonnegative after summing
its quadratic form over all coordinates of a finite-dimensional vector. -/
lemma coordinateMatrixQuadratic_nonneg {m : ℕ} {I : Type*}
    [Fintype I] (M : Matrix I I ℝ) (hM : M.PosSemidef)
    (Z : I → Fin m → ℝ) :
    0 ≤ ∑ a : Fin m, ∑ i, ∑ j, M i j * Z i a * Z j a := by
  -- Apply the scalar PSD inequality to each Euclidean coordinate.
  classical
  apply Finset.sum_nonneg
  intro a ha
  have hcoordinate := hM.dotProduct_mulVec_nonneg (fun i ↦ Z i a)
  -- Expanding the matrix-vector product identifies the scalar quadratic form.
  simpa only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using hcoordinate

/-- A finite-memory certificate gives the vector-valued storage descent after
the scalar certificate inequality is summed coordinatewise. -/
theorem certificateCoordinateDescent {m ℓ : ℕ} {gamma : ℝ}
    (c : Certificate ℓ gamma)
    (Z : (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ) :
    0 ≤
      coordinateQuadraticStorage c.P (fun i ↦ Z (i.1.succ, i.2)) -
        coordinateQuadraticStorage c.P (fun i ↦ Z (i.1.castSucc, i.2)) -
          coordinateSupply gamma c.omega c.epsilon c.lagMinus c.lagPlus Z := by
  -- The certificate's scalar descent theorem applies independently to every
  -- coordinate of the vector history.
  have hscalar := (c.descent_iff.mp c.descent_psd)
  have hcoordinates : 0 ≤ ∑ a : Fin m,
      (quadraticStorage c.P (fun i ↦ Z (i.1.succ, i.2) a) -
        quadraticStorage c.P (fun i ↦ Z (i.1.castSucc, i.2) a) -
          supply gamma c.omega c.epsilon c.lagMinus c.lagPlus
            (fun i ↦ Z i a)) := by
    apply Finset.sum_nonneg
    intro a ha
    exact hscalar (fun i ↦ Z i a)
  -- Distribute the finite coordinate sum across the two storage differences.
  simpa only [coordinateQuadraticStorage, coordinateSupply,
    ← Finset.sum_sub_distrib] using hcoordinates

/-- The lower certificate matrix is nonnegative on every vector history after
coordinatewise lifting. -/
theorem certificateCoordinateLowerMatrix_nonneg {m ℓ : ℕ} {gamma : ℝ}
    (c : Certificate ℓ gamma)
    (Z : (Fin (ℓ + 1) × Fin 2) → Fin m → ℝ) :
    0 ≤ ∑ a : Fin m, ∑ i, ∑ j,
      lowerMatrix gamma c.zeta c.P c.μ i j * Z i a * Z j a := by
  -- Lift the stored lower PSD test by the generic coordinatewise argument.
  exact coordinateMatrixQuadratic_nonneg _ c.lower_psd Z

/-- The lower certificate test bounds vector quadratic storage by the summed
directed interpolation terms and the squared current coordinates. -/
theorem certificateCoordinateLowerBound {m ℓ : ℕ} {gamma : ℝ}
    (c : Certificate ℓ gamma)
    (Z : (Fin (ℓ + 1) × Fin 2) → Fin m → ℝ) :
    0 ≤ coordinateQuadraticStorage c.P Z -
      (∑ a : Fin m, ∑ b : Block,
        ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          (c.μ b i j : ℝ) *
            (-interpolationNormal gamma b j (fun k ↦ Z k a) *
              (interpolationPosition b i (fun k ↦ Z k a) -
                interpolationPosition b j (fun k ↦ Z k a)))) -
        c.zeta *
          ∑ a : Fin m, ((Z (0, 0) a) ^ 2 + (Z (0, 1) a) ^ 2) := by
  -- Begin with the coordinatewise PSD consequence of the lower matrix test.
  have hlower := certificateCoordinateLowerMatrix_nonneg c Z
  -- Expanding each scalar matrix contraction gives the interpolation-gap form.
  simp_rw [lowerMatrix_quadratic] at hlower
  -- Finite-sum distributivity collects the coordinate terms into vector storage.
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hlower
  simpa only [coordinateQuadraticStorage] using hlower

/-- Directed convexity gaps and the certificate lower test give a coercive
lower bound for quadratic storage plus signed objective-value storage. -/
theorem certificateStorageLowerBound {m ℓ : ℕ} {gamma : ℝ}
    (c : Certificate ℓ gamma)
    (Z : (Fin (ℓ + 1) × Fin 2) → Fin m → ℝ)
    (Φ : Block → Option (Fin ℓ) → ℝ) (hΦzero : ∀ b, Φ b none = 0)
    (hgap : ∀ b i j,
      0 ≤ Φ b i - Φ b j -
        ∑ a : Fin m,
          interpolationNormal gamma b j (fun k ↦ Z k a) *
            (interpolationPosition b i (fun k ↦ Z k a) -
              interpolationPosition b j (fun k ↦ Z k a))) :
    0 ≤ coordinateQuadraticStorage c.P Z +
        (∑ b : Block, ∑ j : Fin ℓ,
          lagCoefficient c.lagMinus c.lagPlus b j * Φ b (some j)) -
      c.zeta * ∑ a : Fin m, ((Z (0, 0) a) ^ 2 + (Z (0, 1) a) ^ 2) := by
  classical
  -- Nonnegative certificate weights preserve every directed convexity gap.
  have hweighted : 0 ≤
      ∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
        (c.μ b i j : ℝ) *
          (Φ b i - Φ b j -
            ∑ a : Fin m,
              interpolationNormal gamma b j (fun k ↦ Z k a) *
                (interpolationPosition b i (fun k ↦ Z k a) -
                  interpolationPosition b j (fun k ↦ Z k a))) := by
    apply Finset.sum_nonneg
    intro b hb
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (by positivity) (hgap b i j)
  have hweightedNormalized : 0 ≤
      (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
        (c.μ b i j : ℝ) * (Φ b i - Φ b j)) -
      ∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
        (c.μ b i j : ℝ) *
          ∑ a : Fin m,
            interpolationNormal gamma b j (fun k ↦ Z k a) *
              (interpolationPosition b i (fun k ↦ Z k a) -
                interpolationPosition b j (fun k ↦ Z k a)) := by
    simpa only [mul_sub, Finset.sum_sub_distrib] using hweighted
  -- Commute the coordinate sum past the block and interpolation indices once,
  -- then use that normal contribution to normalize the lower PSD inequality.
  have hsumComm
      (F : Fin m → Block → Option (Fin ℓ) → Option (Fin ℓ) → ℝ) :
      (∑ a : Fin m, ∑ b : Block, ∑ i : Option (Fin ℓ),
          ∑ j : Option (Fin ℓ), F a b i j) =
        ∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          ∑ a : Fin m, F a b i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  have hnormalContribution :
      (∑ a : Fin m, ∑ b : Block,
        ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          (c.μ b i j : ℝ) *
            (-interpolationNormal gamma b j (fun k ↦ Z k a) *
              (interpolationPosition b i (fun k ↦ Z k a) -
                interpolationPosition b j (fun k ↦ Z k a)))) =
        -(∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          (c.μ b i j : ℝ) *
            ∑ a : Fin m,
              interpolationNormal gamma b j (fun k ↦ Z k a) *
                (interpolationPosition b i (fun k ↦ Z k a) -
                  interpolationPosition b j (fun k ↦ Z k a))) := by
    calc
      (∑ a : Fin m, ∑ b : Block,
          ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            (c.μ b i j : ℝ) *
              (-interpolationNormal gamma b j (fun k ↦ Z k a) *
                (interpolationPosition b i (fun k ↦ Z k a) -
                  interpolationPosition b j (fun k ↦ Z k a)))) =
          -(∑ a : Fin m, ∑ b : Block,
            ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
              (c.μ b i j : ℝ) *
                (interpolationNormal gamma b j (fun k ↦ Z k a) *
                  (interpolationPosition b i (fun k ↦ Z k a) -
                    interpolationPosition b j (fun k ↦ Z k a)))) := by
        simp only [neg_mul, mul_neg, Finset.sum_neg_distrib]
      _ = -(∑ b : Block, ∑ i : Option (Fin ℓ),
          ∑ j : Option (Fin ℓ), ∑ a : Fin m,
            (c.μ b i j : ℝ) *
              (interpolationNormal gamma b j (fun k ↦ Z k a) *
                (interpolationPosition b i (fun k ↦ Z k a) -
                  interpolationPosition b j (fun k ↦ Z k a)))) := by
        exact congrArg Neg.neg (hsumComm fun a b i j ↦
          (c.μ b i j : ℝ) *
            (interpolationNormal gamma b j (fun k ↦ Z k a) *
              (interpolationPosition b i (fun k ↦ Z k a) -
                interpolationPosition b j (fun k ↦ Z k a))))
      _ = -(∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          (c.μ b i j : ℝ) *
            ∑ a : Fin m,
              interpolationNormal gamma b j (fun k ↦ Z k a) *
                (interpolationPosition b i (fun k ↦ Z k a) -
                  interpolationPosition b j (fun k ↦ Z k a))) := by
        simp only [Finset.mul_sum]
  have hlower := certificateCoordinateLowerBound c Z
  rw [hnormalContribution] at hlower
  -- Value balance replaces the weighted directed value differences, and the
  -- two nonnegative inequalities then add to the coercive storage bound.
  rw [certificateValueFlow c Φ hΦzero] at hweightedNormalized
  linarith

/-- Current and lagged support inequalities turn the certificate matrix test
into descent of quadratic-plus-value storage with merit and residual terms. -/
theorem certificateStorageDescent {m ℓ : ℕ} {gamma : ℝ}
    (c : Certificate ℓ gamma)
    (Z : (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ)
    (Φ : Block → Fin (ℓ + 1) → ℝ)
    (hcurrent : ∀ b,
      Φ b 0 ≤ ∑ a : Fin m,
        graphNormal gamma b (fun i ↦ Z i a) 0 *
          graphPosition b (fun i ↦ Z i a) 0)
    (hsupport : ∀ b i j,
      Φ b j - Φ b i ≤ ∑ a : Fin m,
        graphNormal gamma b (fun k ↦ Z k a) j *
          (graphPosition b (fun k ↦ Z k a) j -
            graphPosition b (fun k ↦ Z k a) i)) :
    0 ≤
      (coordinateQuadraticStorage c.P (fun i ↦ Z (i.1.succ, i.2)) +
        ∑ b : Block, ∑ j : Fin ℓ,
          lagCoefficient c.lagMinus c.lagPlus b j * Φ b j.succ) -
      (coordinateQuadraticStorage c.P (fun i ↦ Z (i.1.castSucc, i.2)) +
        ∑ b : Block, ∑ j : Fin ℓ,
          lagCoefficient c.lagMinus c.lagPlus b j * Φ b j.castSucc) -
      c.omega * (Φ .F 0 + Φ .J 0) -
      c.epsilon * ∑ a : Fin m, residual (fun i ↦ Z i a) 0 ^ 2 := by
  classical
  -- Positivity of the merit weight converts the two current support bounds
  -- into a lower bound for the current part of the supply.
  have hcurrentSum : Φ .F 0 + Φ .J 0 ≤
      (∑ a : Fin m,
        graphNormal gamma .F (fun i ↦ Z i a) 0 *
          graphPosition .F (fun i ↦ Z i a) 0) +
      ∑ a : Fin m,
        graphNormal gamma .J (fun i ↦ Z i a) 0 *
          graphPosition .J (fun i ↦ Z i a) 0 :=
    add_le_add (hcurrent .F) (hcurrent .J)
  have hcurrentWeighted :=
    mul_le_mul_of_nonneg_left hcurrentSum c.omega_pos.le
  -- Each nonnegative lag weight preserves the corresponding directed support
  -- inequality, and summing gives a lower bound for all lag pairings.
  have hlagPair (b : Block) (d : Fin ℓ) :
      (c.lagMinus b d : ℝ) * (Φ b 0 - Φ b d.succ) +
          (c.lagPlus b d : ℝ) * (Φ b d.succ - Φ b 0) ≤
        (c.lagMinus b d : ℝ) *
            (∑ a : Fin m,
              graphNormal gamma b (fun i ↦ Z i a) 0 *
                (graphPosition b (fun i ↦ Z i a) 0 -
                  graphPosition b (fun i ↦ Z i a) d.succ)) +
          (c.lagPlus b d : ℝ) *
            (∑ a : Fin m,
              graphNormal gamma b (fun i ↦ Z i a) d.succ *
                (graphPosition b (fun i ↦ Z i a) d.succ -
                  graphPosition b (fun i ↦ Z i a) 0)) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hsupport b d.succ 0) (by positivity))
      (mul_le_mul_of_nonneg_left (hsupport b 0 d.succ) (by positivity))
  have hlagSum :
      (∑ b : Block, ∑ d : Fin ℓ,
        ((c.lagMinus b d : ℝ) * (Φ b 0 - Φ b d.succ) +
          (c.lagPlus b d : ℝ) * (Φ b d.succ - Φ b 0))) ≤
        ∑ b : Block, ∑ d : Fin ℓ,
          ((c.lagMinus b d : ℝ) *
              (∑ a : Fin m,
                graphNormal gamma b (fun i ↦ Z i a) 0 *
                  (graphPosition b (fun i ↦ Z i a) 0 -
                    graphPosition b (fun i ↦ Z i a) d.succ)) +
            (c.lagPlus b d : ℝ) *
              (∑ a : Fin m,
                graphNormal gamma b (fun i ↦ Z i a) d.succ *
                  (graphPosition b (fun i ↦ Z i a) d.succ -
                    graphPosition b (fun i ↦ Z i a) 0))) := by
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum
    intro d hd
    exact hlagPair b d
  have hvalueShift :
      (∑ b : Block, ∑ d : Fin ℓ,
        ((c.lagMinus b d : ℝ) * (Φ b 0 - Φ b d.succ) +
          (c.lagPlus b d : ℝ) * (Φ b d.succ - Φ b 0))) =
        (∑ b : Block, ∑ j : Fin ℓ,
          lagCoefficient c.lagMinus c.lagPlus b j * Φ b j.castSucc) -
        ∑ b : Block, ∑ j : Fin ℓ,
          lagCoefficient c.lagMinus c.lagPlus b j * Φ b j.succ := by
    calc
      _ = ∑ b : Block, ∑ j : Fin ℓ,
          lagCoefficient c.lagMinus c.lagPlus b j *
            (Φ b j.castSucc - Φ b j.succ) :=
        lagValueTelescoping c.lagMinus c.lagPlus Φ
      _ = _ := by
        simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hvalueShift] at hlagSum
  -- The coordinate certificate inequality bounds the storage drop by the
  -- complete supply; its expansion and the two support bounds close the goal.
  have hdescent := certificateCoordinateDescent c Z
  rw [coordinateSupply_apply] at hdescent
  linarith

end

end ADMM.ConvergenceProof
